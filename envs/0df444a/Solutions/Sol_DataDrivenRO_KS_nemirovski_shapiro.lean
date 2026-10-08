-- Prove2me | solution 1 for DataDrivenRO.KS.nemirovski_shapiro
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:49:36.577153+00:00
-- url     : https://prove2.me/submissions/b11b89bf-4557-4e68-893a-03742ae82df4

import Mathlib
import Definitions.Def_DataDrivenRO_KS_Setting

open MeasureTheory

namespace D3de75af

lemma integrable_exp_lin (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hsupp : ∃ a b : ℝ, Q (Set.Icc a b)ᶜ = 0) (c : ℝ) :
    Integrable (fun x => Real.exp (c * x)) Q := by
  obtain ⟨a, b, h⟩ := hsupp
  have hae : ∀ᵐ x ∂Q, x ∈ Set.Icc a b := mem_ae_iff.mpr h
  refine Integrable.of_bound (by fun_prop) (Real.exp (|c| * (|a| + |b|))) ?_
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hx' : |x| ≤ |a| + |b| := by
    rw [abs_le]; constructor
    · have := hx.1; have := neg_abs_le a; have := abs_nonneg b; linarith
    · have := hx.2; have := le_abs_self b; have := abs_nonneg a; linarith
  calc c * x ≤ |c * x| := le_abs_self _
    _ = |c| * |x| := abs_mul _ _
    _ ≤ |c| * (|a| + |b|) := mul_le_mul_of_nonneg_left hx' (abs_nonneg _)

end D3de75af

open MeasureTheory in
theorem solution {d : ℕ} (Q : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (Q i)]
    (hsupp : ∀ i, ∃ a b : ℝ, Q i (Set.Icc a b)ᶜ = 0)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : Fin d → ℝ) (lam : ℝ) (hlam : 0 < lam) :
    DataDrivenRO.KS.VaR (Measure.pi Q) ε v ≤
      lam * Real.log (1 / ε) + lam * ∑ i, Real.log (∫ x, Real.exp (v i * x / lam) ∂(Q i)) := by
  set P := Measure.pi Q with hP
  set f : (Fin d → ℝ) → ℝ := fun u => u ⬝ᵥ v with hf
  set M : Fin d → ℝ := fun i => ∫ x, Real.exp (v i * x / lam) ∂(Q i) with hM
  have hint : ∀ i, Integrable (fun x => Real.exp (v i * x / lam)) (Q i) := by
    intro i
    have := D3de75af.integrable_exp_lin (Q i) (hsupp i) (v i / lam)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring_nf
  have hMpos : ∀ i, 0 < M i := fun i => integral_exp_pos (hint i)
  set T := lam * Real.log (1 / ε) + lam * ∑ i, Real.log (M i) with hT
  have hfm : Measurable f := by
    simp only [hf]; fun_prop
  -- exp (f u / lam) = ∏ exp (v i * u i / lam)
  have hexp : ∀ u : Fin d → ℝ, Real.exp (f u / lam) = ∏ i, Real.exp (v i * u i / lam) := by
    intro u
    rw [← Real.exp_sum]
    congr 1
    simp only [hf, dotProduct, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hEint : Integrable (fun u => Real.exp (f u / lam)) P := by
    have := Integrable.fintype_prod (μ := Q) (f := fun i x => Real.exp (v i * x / lam)) hint
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [hexp]
  have hE : ∫ u, Real.exp (f u / lam) ∂P = ∏ i, M i := by
    simp_rw [hexp]
    exact integral_fintype_prod_eq_prod (fun i x => Real.exp (v i * x / lam))
  have hprodpos : 0 < ∏ i, M i := Finset.prod_pos fun i _ => hMpos i
  have hexpT : Real.exp (T / lam) = (1 / ε) * ∏ i, M i := by
    have : T / lam = Real.log (1 / ε) + ∑ i, Real.log (M i) := by
      rw [hT]; field_simp
    rw [this, Real.exp_add, Real.exp_log (by positivity), Real.exp_sum]
    congr 1
    exact Finset.prod_congr rfl fun i _ => Real.exp_log (hMpos i)
  -- Markov
  set S := {u | Real.exp (T / lam) ≤ Real.exp (f u / lam)} with hS
  have hmarkov : Real.exp (T / lam) * P.real S ≤ ∫ u, Real.exp (f u / lam) ∂P :=
    mul_meas_ge_le_integral_of_nonneg (μ := P)
      (Filter.Eventually.of_forall fun u => (Real.exp_pos (f u / lam)).le) hEint (Real.exp (T / lam))
  rw [hE] at hmarkov
  have hbad : P.real S ≤ ε := by
    have h1 : (1 / ε) * ((∏ i, M i) * P.real S) ≤ ∏ i, M i := by
      rw [← mul_assoc, ← hexpT]; exact hmarkov
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hε0] at h1
    have h2 : (∏ i, M i) * (P.real S - ε) ≤ 0 := by nlinarith
    have := nonpos_of_mul_nonpos_right h2 hprodpos
    linarith
  have hsub : {u | T < f u} ⊆ S := by
    intro u hu
    simp only [hS, Set.mem_setOf_eq] at hu ⊢
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hu.le hlam.le)
  have hgt : P.real {u | T < f u} ≤ ε := (measureReal_mono hsub).trans hbad
  have hmem : ENNReal.ofReal (1 - ε) ≤ P {u | f u ≤ T} := by
    have hc : {u | f u ≤ T} = {u | T < f u}ᶜ := by
      ext u; simp
    have hms : MeasurableSet {u | T < f u} := measurableSet_lt measurable_const hfm
    have hr : P.real {u | f u ≤ T} = 1 - P.real {u | T < f u} := by
      rw [hc, probReal_compl_eq_one_sub hms]
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    change 1 - ε ≤ P.real {u | f u ≤ T}
    rw [hr]; linarith
  -- bounded below
  have hbdd : BddBelow {y : ℝ | ENNReal.ofReal (1 - ε) ≤ P {u | f u ≤ y}} := by
    have hten := tendsto_measure_iInter_atTop (μ := P) (s := fun n : ℕ => {u | f u ≤ -(n : ℝ)})
      (fun n => (measurableSet_le hfm measurable_const).nullMeasurableSet)
      (by
        intro m n hmn u hu
        simp only [Set.mem_setOf_eq] at hu ⊢
        have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith)
      ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ n : ℕ, {u : Fin d → ℝ | f u ≤ -(n : ℝ)}) = ∅ := by
      ext u
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
        not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-f u)
      exact ⟨n, by linarith⟩
    rw [hempty, measure_empty] at hten
    have hpos : (0 : ENNReal) < ENNReal.ofReal (1 - ε) := ENNReal.ofReal_pos.mpr (by linarith)
    obtain ⟨n, hn⟩ := (hten.eventually (gt_mem_nhds hpos)).exists
    refine ⟨-(n : ℝ), fun y hy => ?_⟩
    by_contra hlt
    push_neg at hlt
    simp only [Set.mem_setOf_eq] at hy
    have : P {u | f u ≤ y} ≤ P {u | f u ≤ -(n : ℝ)} := by
      apply measure_mono
      intro u hu
      simp only [Set.mem_setOf_eq] at hu ⊢
      linarith
    exact absurd (hy.trans this) (not_le.mpr hn)
  have hVaR : DataDrivenRO.KS.VaR P ε v ≤ T := by
    unfold DataDrivenRO.KS.VaR MultistageStochastic.valueAtRisk
    exact csInf_le hbdd hmem
  exact hVaR
