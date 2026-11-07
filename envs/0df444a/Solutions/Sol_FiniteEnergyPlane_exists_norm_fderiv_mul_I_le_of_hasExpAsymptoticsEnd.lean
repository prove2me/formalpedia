-- Prove2me | solution 1 for FiniteEnergyPlane.exists_norm_fderiv_mul_I_le_of_hasExpAsymptoticsEnd
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T17:22:10.225631+00:00
-- url     : https://prove2.me/submissions/f8960902-211e-4760-8a23-ea8dfda29043

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem iflg_exists_cylInf_eq (z : ℂ) (hz : z ≠ 0) :
    ∃ t : ℝ, cylInf (Real.log ‖z‖ / (2 * π)) t = z := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hexp : Real.exp (2 * π * (Real.log ‖z‖ / (2 * π))) = ‖z‖ := by
    rw [mul_div_cancel₀ _ h2pi.ne', Real.exp_log hzpos]
  refine ⟨Complex.arg z / (2 * π), ?_⟩
  unfold cylInf ccwLoop
  rw [hexp]
  have e : ((2 * π * (Complex.arg z / (2 * π)) : ℝ) : ℂ) = (Complex.arg z : ℂ) := by
    congr 1
    field_simp
  rw [e]
  exact Complex.norm_mul_exp_arg_mul_I z

theorem iflg_hasDerivAt_cylInf (s t : ℝ) :
    HasDerivAt (fun t => cylInf s t) ((2 * π : ℝ) • (cylInf s t * Complex.I)) t := by
  have h1 : HasDerivAt (fun t : ℝ => ((2 * π * t : ℝ) : ℂ) * Complex.I)
      (((2 * π : ℝ) : ℂ) * Complex.I) t := by
    have h0 : HasDerivAt (fun t : ℝ => 2 * π * t) (2 * π) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * π)
    exact h0.ofReal_comp.mul_const Complex.I
  have h2 := (h1.cexp).const_mul ((Real.exp (2 * π * s) : ℝ) : ℂ)
  have e : (2 * π : ℝ) • (cylInf s t * Complex.I) = ((Real.exp (2 * π * s) : ℝ) : ℂ) *
      (Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I) * (((2 * π : ℝ) : ℂ) * Complex.I)) := by
    unfold cylInf ccwLoop
    rw [Complex.real_smul]
    ring
  rw [e]
  exact h2

theorem iflg_differentiable_cylInf : Differentiable ℝ (fun p : ℝ × ℝ => cylInf p.1 p.2) := by
  unfold cylInf ccwLoop
  have h1' : Differentiable ℝ (fun p : ℝ × ℝ => Real.exp (2 * π * p.1)) := by fun_prop
  have h2' : Differentiable ℝ (fun p : ℝ × ℝ => 2 * π * p.2) := by fun_prop
  have h1 : Differentiable ℝ (fun p : ℝ × ℝ => ((Real.exp (2 * π * p.1) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.differentiable.comp h1'
  have h2 : Differentiable ℝ (fun p : ℝ × ℝ => ((2 * π * p.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.differentiable.comp h2'
  exact h1.mul ((h2.mul_const Complex.I).cexp)

theorem exists_norm_fderiv_mul_I_le_of_hasExpAsymptoticsEnd_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (u : ℂ → V n)
    (hw : ContDiff ℝ 1 (fun z => proj H (u z))) (P : ReebOrbit H) (b : ℝ) (hb : 0 < b)
    (hexp : HasExpAsymptoticsEnd H u cylInf P 1 b) :
    ∃ K : ℝ, ∀ z, ‖fderiv ℝ (fun z => proj H (u z)) z (z * Complex.I)‖ ≤ K := by
  set w : ℂ → V n := fun z => proj H (u z) with hwdef
  obtain ⟨d, c, -, hW⟩ := hexp
  obtain ⟨C, s₁, hC⟩ := hW.2 1
  have hwd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hxc : Continuous (deriv P.x) :=
    (P.contDiff_x H hH).continuous_deriv (by simp)
  have hper : Function.Periodic (deriv P.x) P.T := by
    intro τ
    rw [(P.hasDerivAt (τ + P.T)).deriv, (P.hasDerivAt τ).deriv, P.periodic]
  obtain ⟨M, hM⟩ := (isBounded_iff_forall_norm_le.1
    (hper.compact_of_continuous P.T_pos.ne' hxc).isBounded)
  have hMd : ∀ τ, ‖deriv P.x τ‖ ≤ M := fun τ => hM _ ⟨τ, rfl⟩
  set f : ℝ × ℝ → V n := fun p => endW H u cylInf p - P.x (1 * P.T * p.2 + c) with hf
  have hfd : ∀ p, DifferentiableAt ℝ f p := by
    intro p
    have h1 : DifferentiableAt ℝ (endW H u cylInf) p :=
      (hwd _).comp p (iflg_differentiable_cylInf p)
    have h2 : DifferentiableAt ℝ (fun p : ℝ × ℝ => P.x (1 * P.T * p.2 + c)) p :=
      DifferentiableAt.comp p (P.hasDerivAt _).differentiableAt (by fun_prop)
    exact h1.sub h2
  have hkey : ∀ s t : ℝ, (2 * π) • fderiv ℝ w (cylInf s t) (cylInf s t * Complex.I) -
      P.T • deriv P.x (1 * P.T * t + c) = fderiv ℝ f (s, t) (0, 1) := by
    intro s t
    have hl : HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) t :=
      (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
    have h1 : HasDerivAt (fun t => f (s, t)) (fderiv ℝ f (s, t) (0, 1)) t :=
      (hfd (s, t)).hasFDerivAt.comp_hasDerivAt t hl
    have h2 : HasDerivAt (fun t => w (cylInf s t))
        (fderiv ℝ w (cylInf s t) ((2 * π : ℝ) • (cylInf s t * Complex.I))) t :=
      (hwd _).hasFDerivAt.comp_hasDerivAt t (iflg_hasDerivAt_cylInf s t)
    have h3 : HasDerivAt (fun t : ℝ => P.x (1 * P.T * t + c))
        (P.T • deriv P.x (1 * P.T * t + c)) t := by
      have h0 : HasDerivAt (fun t : ℝ => 1 * P.T * t + c) P.T t := by
        simpa using ((hasDerivAt_id t).const_mul (1 * P.T)).add_const c
      exact (P.contDiff_x H hH).differentiable (by simp) _ |>.hasDerivAt.scomp t h0
    have h4 := h2.sub h3
    rw [map_smul] at h4
    exact h4.unique h1
  set s₂ := max s₁ 0 with hs₂
  set R₁ := Real.exp (2 * π * s₂) with hR₁
  have hcont : Continuous (fun z => fderiv ℝ w z (z * Complex.I)) :=
    (hw.continuous_fderiv (by norm_num)).clm_apply (continuous_id.mul continuous_const)
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall (0 : ℂ) R₁).exists_bound_of_continuousOn
    hcont.continuousOn
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  refine ⟨max K₀ ((|C| + P.T * M) / (2 * π)), fun z => ?_⟩
  by_cases hz : ‖z‖ ≤ R₁
  · exact (hK₀ z (mem_closedBall_zero_iff.2 hz)).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    push_neg at hz
    have hzpos : 0 < ‖z‖ := lt_trans (Real.exp_pos _) hz
    have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
    obtain ⟨t, ht⟩ := iflg_exists_cylInf_eq z hz0
    set s := Real.log ‖z‖ / (2 * π) with hsdef
    have hss : s₂ ≤ s := by
      rw [hsdef, le_div_iff₀ h2pi]
      have : 2 * π * s₂ ≤ Real.log ‖z‖ := by
        rw [Real.le_log_iff_exp_le hzpos]
        exact hz.le
      linarith
    have hs1 : s₁ ≤ s := (le_max_left _ _).trans hss
    have hs0 : 0 ≤ s := (le_max_right _ _).trans hss
    have hb1 : Real.exp (-(b * s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := mul_nonneg hb.le hs0
      linarith
    have hf1 := hC s hs1 t
    rw [norm_iteratedFDeriv_one] at hf1
    have hf2 : ‖fderiv ℝ f (s, t)‖ ≤ |C| := by
      refine hf1.trans ?_
      calc C * Real.exp (-(b * s)) ≤ |C| * Real.exp (-(b * s)) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
        _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hb1 (abs_nonneg C)
        _ = |C| := mul_one _
    have hn01 : ‖((0, 1) : ℝ × ℝ)‖ = 1 := by simp
    have hf3 : ‖fderiv ℝ f (s, t) (0, 1)‖ ≤ |C| := by
      have := (fderiv ℝ f (s, t)).le_opNorm (0, 1)
      rw [hn01, mul_one] at this
      exact this.trans hf2
    have hk := hkey s t
    rw [ht] at hk
    have heq : (2 * π) • fderiv ℝ w z (z * Complex.I) =
        fderiv ℝ f (s, t) (0, 1) + P.T • deriv P.x (1 * P.T * t + c) := by
      rw [← hk, sub_add_cancel]
    have hnorm : (2 * π) * ‖fderiv ℝ w z (z * Complex.I)‖ ≤ |C| + P.T * M := by
      have h := norm_smul (2 * π) (fderiv ℝ w z (z * Complex.I))
      rw [Real.norm_eq_abs, abs_of_pos h2pi] at h
      rw [← h, heq]
      refine (norm_add_le _ _).trans (add_le_add hf3 ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos P.T_pos]
      exact mul_le_mul_of_nonneg_left (hMd _) P.T_pos.le
    rw [le_div_iff₀ h2pi]
    linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (u : ℂ → V n)
    (hw : ContDiff ℝ 1 (fun z => proj H (u z))) (P : ReebOrbit H) (b : ℝ) (hb : 0 < b)
    (hexp : HasExpAsymptoticsEnd H u cylInf P 1 b) :
    ∃ K : ℝ, ∀ z, ‖fderiv ℝ (fun z => proj H (u z)) z (z * Complex.I)‖ ≤ K :=
  exists_norm_fderiv_mul_I_le_of_hasExpAsymptoticsEnd_aux H hH u hw P b hb hexp
