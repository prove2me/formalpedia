-- Prove2me | solution 1 for CachonPushPull.Pareto.pull_supplier_increasing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:10:28.915771+00:00
-- url     : https://prove2.me/submissions/a492eb7f-9a6d-4676-ad77-4a7613f20cfe

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

lemma aux_psi_one_sub_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (y : ℝ) (hy : 0 ≤ y) : 0 < 1 - cdf μ y := by
  have h1 : cdf μ y < cdf μ (y + 1) :=
    hD.strictMonoOn (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr (by linarith)) (by linarith)
  have h2 := cdf_le_one μ (y + 1)
  linarith

lemma aux_psi_S_hasDerivAt (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (q : ℝ) (hq : 0 < q) :
    HasDerivAt (S μ) (1 - cdf μ q) q := by
  have hmono : Monotone (cdf μ) := monotone_cdf μ
  have hI : HasDerivAt (fun u => ∫ x in (0:ℝ)..u, cdf μ x) (cdf μ q) q :=
    intervalIntegral.integral_hasDerivAt_right hmono.intervalIntegrable
      hmono.measurable.stronglyMeasurable.stronglyMeasurableAtFilter
      (hD.hasDerivAt q hq).continuousAt
  have := (hasDerivAt_id' q).fun_sub hI
  show HasDerivAt (fun y => y - ∫ x in (0:ℝ)..y, cdf μ x) (1 - cdf μ q) q
  exact this

lemma aux_psi_S_continuous (μ : Measure ℝ) : Continuous (S μ) := by
  have hmono : Monotone (cdf μ) := monotone_cdf μ
  have := intervalIntegral.continuous_primitive (μ := volume)
    (fun a b => hmono.intervalIntegrable (a := a) (b := b)) 0
  unfold S
  exact continuous_id.sub this

lemma aux_psi_S_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (q : ℝ) (hq : 0 < q) : 0 < S μ q := by
  have hmono : Monotone (cdf μ) := monotone_cdf μ
  have hle : (∫ x in (0:ℝ)..q, cdf μ x) ≤ ∫ x in (0:ℝ)..q, cdf μ q :=
    intervalIntegral.integral_mono_on hq.le hmono.intervalIntegrable
      intervalIntegrable_const (fun x hx => hmono hx.2)
  rw [intervalIntegral.integral_const] at hle
  have hpos := aux_psi_one_sub_pos μ f hD q hq.le
  unfold S
  simp only [smul_eq_mul, sub_zero] at hle
  nlinarith

lemma aux_psi_f_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (x : ℝ) (hx : 0 < x) : 0 < f x := by
  set g : ℝ → ℝ := fun y : ℝ => y * f y / (1 - cdf μ y) with hg
  have hfnn : ∀ y, 0 < y → 0 ≤ f y := by
    intro y hy
    have := (monotone_cdf μ).deriv_nonneg (x := y)
    rwa [(hD.hasDerivAt y hy).deriv] at this
  have hgnn : ∀ y, 0 < y → 0 ≤ g y := by
    intro y hy
    have := aux_psi_one_sub_pos μ f hD y hy.le
    have := hfnn y hy
    simp only [hg]
    positivity
  have hdiff : ∀ y, 0 < y → DifferentiableAt ℝ g y := fun y hy =>
    differentiableAt_of_deriv_ne_zero (hD.igfr y hy).ne'
  have hsm : StrictMonoOn g (Set.Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · exact fun y hy => (hdiff y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioi] at hy
      exact hD.igfr y hy
  rcases (hfnn x hx).lt_or_eq with h | h
  · exact h
  · exfalso
    have hgx : g x = 0 := by simp [hg, ← h]
    have hlt := hsm (Set.mem_Ioi.mpr (by linarith : (0:ℝ) < x / 2)) (Set.mem_Ioi.mpr hx)
      (by linarith : x / 2 < x)
    have := hgnn (x / 2) (by linarith)
    linarith

lemma aux_psi_fun (μ : Measure ℝ) (c v : ℝ) : pullSupplierProfit μ c v =
    fun y => ((c - v * cdf μ y) / (1 - cdf μ y) - v) * S μ y - (c - v) * y := by
  funext y
  simp [pullSupplierProfit, pullSupplierProfitAt, pullPrice]

lemma aux_psi_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) (q : ℝ) (hq : 0 < q) :
    HasDerivAt (pullSupplierProfit μ c v)
      ((p - v) * (1 - cdf μ qo) * j μ q * hazard μ f q) q := by
  have hF := hD.hasDerivAt q hq
  have hS := aux_psi_S_hasDerivAt μ f hD q hq
  have hne : 1 - cdf μ q ≠ 0 := (aux_psi_one_sub_pos μ f hD q hq.le).ne'
  have hden : HasDerivAt (fun y => 1 - cdf μ y) (0 - f q) q := (hasDerivAt_const q 1).sub hF
  have hnum : HasDerivAt (fun y => c - v * cdf μ y) (0 - v * f q) q :=
    (hasDerivAt_const q c).sub (hF.const_mul v)
  have hP := ((hnum.fun_div hden hne).fun_sub (hasDerivAt_const q v)).fun_mul hS
  have hT := hP.fun_sub ((hasDerivAt_id' q).const_mul (c - v))
  rw [aux_psi_fun]
  refine hT.congr_deriv ?_
  have hpv : p - v ≠ 0 := by linarith
  rw [hqo]
  simp only [j, hazard]
  field_simp
  ring

theorem aux_psi_main (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) :
    (∀ q : ℝ, 0 < q → HasDerivAt (pullSupplierProfit μ c v)
      ((p - v) * (1 - cdf μ qo) * j μ q * hazard μ f q) q) ∧
    StrictMonoOn (pullSupplierProfit μ c v) (Set.Ici 0) := by
  have hderiv := aux_psi_deriv μ f hD p c v hvc hcp qo hqo
  refine ⟨hderiv, ?_⟩
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro x hx
    rcases (Set.mem_Ici.mp hx).lt_or_eq with h | h
    · exact (hderiv x h).continuousAt.continuousWithinAt
    · subst h
      have hFc : ContinuousWithinAt (cdf μ) (Set.Ici 0) 0 := (cdf μ).right_continuous 0
      have hSc : ContinuousWithinAt (S μ) (Set.Ici 0) 0 :=
        (aux_psi_S_continuous μ).continuousAt.continuousWithinAt
      have hne : 1 - cdf μ 0 ≠ 0 := by rw [hD.cdf_zero]; norm_num
      have := ((((continuousWithinAt_const (b := c)).sub
        ((continuousWithinAt_const (b := v)).mul hFc)).div
        ((continuousWithinAt_const (b := (1:ℝ))).sub hFc) hne).sub
        (continuousWithinAt_const (b := v))).mul hSc |>.sub
        ((continuousWithinAt_const (b := c - v)).mul continuousWithinAt_id)
      rw [aux_psi_fun]
      exact this
  · intro x hx
    rw [interior_Ici] at hx
    have hx' : 0 < x := hx
    rw [(hderiv x hx').deriv]
    have h1 : 0 < 1 - cdf μ x := aux_psi_one_sub_pos μ f hD x hx'.le
    have hpv : 0 < p - v := by linarith
    have h2 : (p - v) * (1 - cdf μ qo) = c - v := by
      rw [hqo]; field_simp; ring
    rw [h2]
    have hS := aux_psi_S_pos μ f hD x hx'
    have hf := aux_psi_f_pos μ f hD x hx'
    have hcv : 0 < c - v := by linarith
    simp only [j, hazard]
    positivity

end CachonPushPull.Pareto

open CachonPushPull.Pareto
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) :
    (∀ q : ℝ, 0 < q → HasDerivAt (pullSupplierProfit μ c v)
      ((p - v) * (1 - cdf μ qo) * j μ q * hazard μ f q) q) ∧
    StrictMonoOn (pullSupplierProfit μ c v) (Set.Ici 0) :=
  aux_psi_main μ f hD p c v hvc hcp qo hqo
