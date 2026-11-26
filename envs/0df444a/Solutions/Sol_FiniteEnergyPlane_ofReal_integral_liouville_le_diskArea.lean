-- Prove2me | solution 1 for FiniteEnergyPlane.ofReal_integral_liouville_le_diskArea
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T21:53:06.728202+00:00
-- url     : https://prove2.me/submissions/cfece59c-4111-4adc-a6c3-bd637c51f7cb

import Definitions.Def_FiniteEnergyPlane_SpanningDisk
import Mathlib
import Theorems.Thm_FlowCalculus_exists_continuous_bijective_complete_flow
import Theorems.Thm_FlowCalculus_contDiff_complete_solution_family
import Theorems.Thm_FiniteEnergyPlane_hasDerivAt_wedge_flow
import Theorems.Thm_FiniteEnergyPlane_charField_div_eq_omega0
import Theorems.Thm_FiniteEnergyPlane_ofReal_integral_le_lintegral_of_injOn_sweep
import Theorems.Thm_FiniteEnergyPlane_exists_exitTime_of_leavesRadiateFrom
import Theorems.Thm_FiniteEnergyPlane_injOn_leafSweep



/-! Glue for P c5a21fab `ofReal_integral_liouville_le_diskArea` (leaf sweep). -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal Real

theorem olp_liou_add (x v w : V 1) : liouville x (v + w) = liouville x v + liouville x w := by
  simp only [liouville, omega0, dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring

theorem olp_liou_smul (x v : V 1) (a : ℝ) : liouville x (a • v) = a * liouville x v := by
  simp only [liouville, omega0, dot, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem olp_liou_eq (e : ℂ → V 1) (z w : ℂ) :
    liouville (e z) (fderiv ℝ e z w) = (charField e z).re * w.im - (charField e z).im * w.re := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul, olp_liou_add, olp_liou_smul, olp_liou_smul]
  simp only [charField, ds, dt]
  ring

theorem olp_liou_contDiff (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) (w : ℂ) :
    ContDiff ℝ ∞ (fun z => liouville (e z) (fderiv ℝ e z w)) := by
  have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ e z w) :=
    (he.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  unfold liouville omega0 dot
  refine ContDiff.div_const (ContDiff.sum fun k _ => ContDiff.mul ?_ ((contDiff_apply ℝ ℝ k).comp hd)) _
  unfold j0
  split_ifs
  · exact ((contDiff_apply ℝ ℝ _).comp he).neg
  · exact (contDiff_apply ℝ ℝ _).comp he

theorem olp_charField_contDiff (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) :
    ContDiff ℝ ∞ (charField e) := by
  have h : charField e = fun z => ((liouville (e z) (fderiv ℝ e z Complex.I) : ℝ) : ℂ) +
      ((-liouville (e z) (fderiv ℝ e z 1) : ℝ) : ℂ) * Complex.I := by
    funext z; apply Complex.ext <;> simp [charField, ds, dt]
  rw [h]
  exact (Complex.ofRealCLM.contDiff.comp (olp_liou_contDiff e he _)).add
    ((Complex.ofRealCLM.contDiff.comp (olp_liou_contDiff e he _).neg).mul contDiff_const)

/-- Partial derivatives of a jointly differentiable two-variable map. -/
theorem olp_fderiv_snd (Ψ : ℝ × ℂ → ℂ) (hΨ : Differentiable ℝ Ψ) (τ : ℝ) (z v : ℂ) :
    fderiv ℝ (fun y => Ψ (τ, y)) z v = fderiv ℝ Ψ (τ, z) (0, v) := by
  have h : HasFDerivAt (fun y => Ψ (τ, y))
      ((fderiv ℝ Ψ (τ, z)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)) z :=
    (hΨ (τ, z)).hasFDerivAt.comp z (hasFDerivAt_prodMk_right τ z)
  rw [h.fderiv]; rfl

theorem olp_fderiv_fst (Ψ : ℝ × ℂ → ℂ) (hΨ : Differentiable ℝ Ψ) (τ : ℝ) (z : ℂ) (d : ℂ)
    (hd : HasDerivAt (fun s => Ψ (s, z)) d τ) : fderiv ℝ Ψ (τ, z) (1, 0) = d := by
  have h1 : HasDerivAt (fun s : ℝ => (s, z)) ((1 : ℝ), (0 : ℂ)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ z)
  exact ((hΨ (τ, z)).hasFDerivAt.comp_hasDerivAt τ h1).unique hd

theorem ofReal_integral_liouville_le_diskArea_aux (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) (z₀ : ℂ)
    (hz₀ : z₀ ∈ ball (0 : ℂ) 1) (hV : charField e z₀ = 0) (hL : LeavesRadiateFrom e z₀)
    (hS : ∀ z ∈ sphere (0 : ℂ) 1, 0 < liouville (e z) (fderiv ℝ e z (Complex.I * z)))
    (c : ℝ → ℂ) (hc : ContDiff ℝ 1 c) (hcA : ∀ t, c t ∈ closedBall (0 : ℂ) 1)
    (hw : HasLoopWind (fun t => c t - z₀) 1)
    (htr : ∀ t, liouville (e (c t)) (fderiv ℝ e (c t) (deriv c t)) ≠ 0) :
    ENNReal.ofReal (∫ t in (0 : ℝ)..1, liouville (e (c t)) (fderiv ℝ e (c t) (deriv c t))) ≤
      diskArea e := by
  -- the cut-off characteristic field
  let χ : ContDiffBump (0 : ℂ) := ⟨2, 3, by norm_num, by norm_num⟩
  set X : ℂ → ℂ := fun z => ((χ z : ℝ) : ℂ) * charField e z with hXdef
  have hVc := olp_charField_contDiff e he
  have hX : ContDiff ℝ ∞ X := (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul hVc
  have hXK : HasCompactSupport X := by
    have : HasCompactSupport (fun z => ((χ z : ℝ) : ℂ)) :=
      χ.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    exact this.mul_right
  have hXV : ∀ z ∈ ball (0 : ℂ) 2, X z = charField e z := by
    intro z hz
    have : χ z = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hz)
    simp [hXdef, this]
  have hXev : ∀ z ∈ ball (0 : ℂ) 2, X =ᶠ[𝓝 z] charField e := fun z hz =>
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) hXV
  -- its flow
  obtain ⟨ψ, hψc, -, hψ0, -, hψd⟩ := FlowCalculus.exists_continuous_bijective_complete_flow
    (fun _ y => X y) (hX.comp contDiff_snd)
    ⟨tsupport X, hXK, fun _ y hy => image_eq_zero_of_notMem_tsupport hy⟩
  have hψd' : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t := hψd
  have hψs : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ψ p.1 p.2) :=
    FlowCalculus.contDiff_complete_solution_family (fun _ y => X y) ψ (hX.comp contDiff_snd)
      hψc hψ0 hψd
  set Ψ : ℝ × ℂ → ℂ := fun p => ψ p.1 p.2 with hΨdef
  have hΨd : Differentiable ℝ Ψ := hψs.differentiable (by simp)
  obtain ⟨b, -, hb⟩ := exists_exitTime_of_leavesRadiateFrom e he z₀ hz₀ hV hL hS X hX hXK hXV ψ
    hψc hψ0 hψd'
  have hinj := injOn_leafSweep e he z₀ hz₀ hV hL hS X hX hXK hXV ψ hψs hψ0 hψd' c hc hcA hw htr
  have hcz : ∀ t, c t ≠ z₀ := fun t h => hw.2.2.1 t (by simp [h])
  have hcl : ∀ s ≤ (0 : ℝ), ∀ t, ψ s (c t) ∈ closedBall (0 : ℂ) 1 := by
    intro s hs t
    obtain ⟨hb0, hlt, hsph, -⟩ := hb (c t) (hcA t) (hcz t)
    rcases lt_or_ge s (b (c t)) with h | h
    · exact ball_subset_closedBall (hlt s h)
    · have hs' : s = b (c t) := le_antisymm (hs.trans hb0) h
      rw [hs']; exact sphere_subset_closedBall hsph
  -- the sweep and its derivative
  have hcd : ∀ t, HasDerivAt c (deriv c t) t := fun t =>
    ((hc.differentiable (by norm_num)) t).hasDerivAt
  set G : ℂ → ℂ := fun p => ψ p.re (c p.im) with hGdef
  let L : ℂ → ℂ →L[ℝ] ℝ × ℂ := fun p =>
    Complex.reCLM.prod ((ContinuousLinearMap.toSpanSingleton ℝ (deriv c p.im)).comp Complex.imCLM)
  have hLd : ∀ p : ℂ, HasFDerivAt (fun q : ℂ => (q.re, c q.im)) (L p) p := by
    intro p
    refine Complex.reCLM.hasFDerivAt.prodMk ?_
    have := (hcd p.im).hasFDerivAt.comp p Complex.imCLM.hasFDerivAt
    exact this
  set G' : ℂ → ℂ →L[ℝ] ℂ := fun p => (fderiv ℝ Ψ (p.re, c p.im)).comp (L p) with hG'def
  have hG : ∀ p, HasFDerivAt G (G' p) p := fun p => by
    have := HasFDerivAt.comp p (g := Ψ) (hΨd (p.re, c p.im)).hasFDerivAt (hLd p)
    exact this
  have hG'1 : ∀ p, G' p 1 = X (G p) := by
    intro p
    have : G' p 1 = fderiv ℝ Ψ (p.re, c p.im) (1, 0) := by simp [hG'def, L]
    rw [this]
    exact olp_fderiv_fst Ψ hΨd p.re (c p.im) _ (hψd' p.re (c p.im))
  have hG'I : ∀ p, G' p Complex.I = fderiv ℝ (ψ p.re) (c p.im) (deriv c p.im) := by
    intro p
    have : G' p Complex.I = fderiv ℝ Ψ (p.re, c p.im) (0, deriv c p.im) := by simp [hG'def, L]
    rw [this, ← olp_fderiv_snd Ψ hΨd p.re (c p.im) (deriv c p.im)]
  -- the Jacobian
  set J : ℂ → ℝ := fun p => (X (ψ p.re (c p.im))).re * (fderiv ℝ (ψ p.re) (c p.im) (deriv c p.im)).im -
      (X (ψ p.re (c p.im))).im * (fderiv ℝ (ψ p.re) (c p.im) (deriv c p.im)).re with hJdef
  have hJ : ∀ p, J p = (G' p 1).re * (G' p Complex.I).im - (G' p 1).im * (G' p Complex.I).re := by
    intro p; rw [hG'1, hG'I]
  have hJc : Continuous J := by
    have hD : Continuous (fun p : ℂ => fderiv ℝ (ψ p.re) (c p.im) (deriv c p.im)) := by
      have : (fun p : ℂ => fderiv ℝ (ψ p.re) (c p.im) (deriv c p.im)) =
          fun p => fderiv ℝ Ψ (p.re, c p.im) (0, deriv c p.im) := by
        funext p; exact olp_fderiv_snd Ψ hΨd p.re (c p.im) (deriv c p.im)
      rw [this]
      have hcc : Continuous c := hc.continuous
      have hdc : Continuous (deriv c) := hc.continuous_deriv le_rfl
      exact ((hψs.continuous_fderiv (by simp)).comp
        (Complex.continuous_re.prodMk (hcc.comp Complex.continuous_im))).clm_apply
        (continuous_const.prodMk (hdc.comp Complex.continuous_im))
    have hXG : Continuous (fun p : ℂ => X (ψ p.re (c p.im))) :=
      hX.continuous.comp (hψc.comp (Complex.continuous_re.prodMk
        (hc.continuous.comp Complex.continuous_im)))
    exact ((Complex.continuous_re.comp hXG).mul (Complex.continuous_im.comp hD)).sub
      ((Complex.continuous_im.comp hXG).mul (Complex.continuous_re.comp hD))
  set f : ℂ → ℝ := fun z => omega0 (ds e z) (dt e z) with hfdef
  have hf : Continuous f := by
    have hds : ContDiff ℝ ∞ (fun z => ds e z) :=
      (he.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have hdt : ContDiff ℝ ∞ (fun z => dt e z) :=
      (he.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    unfold omega0 dot at hfdef
    rw [hfdef]
    refine continuous_finset_sum _ fun k _ => Continuous.mul ?_ ((continuous_apply k).comp hdt.continuous)
    unfold j0
    split_ifs
    · exact ((continuous_apply _).comp hds.continuous).neg
    · exact (continuous_apply _).comp hds.continuous
  have hJd : ∀ p : ℂ, p.re ≤ 0 → p.im ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun τ : ℝ => J (τ + p.im * Complex.I)) (f (G p) * J p) p.re := by
    intro p hp _
    have h := hasDerivAt_wedge_flow X hX ψ hψs hψd' p.re (c p.im) (deriv c p.im)
    have hGb : G p ∈ ball (0 : ℂ) 2 :=
      mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 (hcl p.re hp p.im)) (by norm_num))
    have hdiv : (fderiv ℝ X (G p) 1).re + (fderiv ℝ X (G p) Complex.I).im = f (G p) := by
      rw [(hXev _ hGb).fderiv_eq]; exact charField_div_eq_omega0 e he (G p)
    have hfun : (fun τ : ℝ => J (τ + p.im * Complex.I)) = fun s =>
        (X (ψ s (c p.im))).re * (fderiv ℝ (ψ s) (c p.im) (deriv c p.im)).im -
          (X (ψ s (c p.im))).im * (fderiv ℝ (ψ s) (c p.im) (deriv c p.im)).re := by
      funext τ; simp [hJdef]
    rw [hfun, ← hdiv]
    exact h
  have hmaps : MapsTo G {p : ℂ | p.re < 0 ∧ p.im ∈ Ico (0 : ℝ) 1} (ball 0 1) := by
    intro p hp
    obtain ⟨hb0, hlt, -⟩ := hb (c p.im) (hcA _) (hcz _)
    exact hlt p.re (hp.1.trans_le hb0)
  have hψ0' : ψ 0 = id := funext hψ0
  have hpt : ∀ t : ℝ, J (t * Complex.I) = liouville (e (c t)) (fderiv ℝ e (c t) (deriv c t)) := by
    intro t
    have hXc : X (c t) = charField e (c t) :=
      hXV _ (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 (hcA t)) (by norm_num)))
    simp only [hJdef, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero, zero_mul, hψ0',
      fderiv_id, fderiv_id', id, ContinuousLinearMap.id_apply]
    rw [olp_liou_eq, hXc]
  have hint : (∫ t in (0 : ℝ)..1, J (t * Complex.I)) =
      ∫ t in (0 : ℝ)..1, liouville (e (c t)) (fderiv ℝ e (c t) (deriv c t)) :=
    intervalIntegral.integral_congr fun t _ => hpt t
  rw [← hint]
  -- the sign of the transverse loop is constant
  have hαc : Continuous (fun t : ℝ => J (t * Complex.I)) :=
    hJc.comp (Complex.continuous_ofReal.mul continuous_const)
  by_cases hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < J (t * Complex.I)
  · exact ofReal_integral_le_lintegral_of_injOn_sweep G G' hG J hJ hJc f hf hJd hpos hinj hmaps
  · push_neg at hpos
    obtain ⟨t₀, ht₀, h₀⟩ := hpos
    have hne : ∀ t : ℝ, J (t * Complex.I) ≠ 0 := fun t => by rw [hpt]; exact htr t
    have h₀' : J (t₀ * Complex.I) < 0 := lt_of_le_of_ne h₀ (hne t₀)
    have hneg : ∀ t ∈ Icc (0 : ℝ) 1, J (t * Complex.I) ≤ 0 := by
      intro t ht
      by_contra hlt
      push_neg at hlt
      have hsub := intermediate_value_uIcc (a := t₀) (b := t) hαc.continuousOn
      have h0mem : (0 : ℝ) ∈ uIcc (J (t₀ * Complex.I)) (J (t * Complex.I)) :=
        mem_uIcc.2 (Or.inl ⟨h₀'.le, hlt.le⟩)
      obtain ⟨s, -, hs⟩ := hsub h0mem
      exact hne s hs
    have hle : (∫ t in (0 : ℝ)..1, J (t * Complex.I)) ≤ 0 := by
      have := intervalIntegral.integral_nonneg (μ := volume) (f := fun t => -J (t * Complex.I))
        zero_le_one (fun t ht => neg_nonneg.2 (hneg t ht))
      rw [intervalIntegral.integral_neg] at this
      linarith
    rw [ENNReal.ofReal_of_nonpos hle]
    exact bot_le

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

theorem solution (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) (z₀ : ℂ)
    (hz₀ : z₀ ∈ ball (0 : ℂ) 1) (hV : charField e z₀ = 0) (hL : LeavesRadiateFrom e z₀)
    (hS : ∀ z ∈ sphere (0 : ℂ) 1, 0 < liouville (e z) (fderiv ℝ e z (Complex.I * z)))
    (c : ℝ → ℂ) (hc : ContDiff ℝ 1 c) (hcA : ∀ t, c t ∈ closedBall (0 : ℂ) 1)
    (hw : HasLoopWind (fun t => c t - z₀) 1)
    (htr : ∀ t, liouville (e (c t)) (fderiv ℝ e (c t) (deriv c t)) ≠ 0) :
    ENNReal.ofReal (∫ t in (0 : ℝ)..1, liouville (e (c t)) (fderiv ℝ e (c t) (deriv c t))) ≤
      diskArea e :=
  ofReal_integral_liouville_le_diskArea_aux e he z₀ hz₀ hV hL hS c hc hcA hw htr
