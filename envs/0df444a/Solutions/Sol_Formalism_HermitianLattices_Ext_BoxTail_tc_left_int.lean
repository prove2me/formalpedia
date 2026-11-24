-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tc_left_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:26.072698+00:00
-- url     : https://prove2.me/submissions/1c0deba1-7206-4741-9656-271a938ad195

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContourB
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tc_left_pt
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tc_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z η σ T M : ℝ)
    (hz : 0 < z) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1 - 1 / 800) (hT : 0 ≤ T)
    (hL : ∀ u : ℝ, |u| ≤ T → DirichletCharacter.LFunction χ ((σ : ℂ) + (u : ℂ) * I) ≠ 0)
    (hM : ∀ u : ℝ, |u| ≤ T → ‖Formalism.ZeroFreeDirichlet.negLD χ ((σ : ℂ) + (u : ℂ) * I)‖ ≤ M) :
    ‖(∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ (z + z * η) ((σ : ℂ) + (u : ℂ) * I))
      - ∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ z ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      M * (4 * η * z ^ σ) * (4 * Real.log (1 + 800 * T)) := by
  set δ : ℝ := 1 - σ with hδ
  have hδpos : 0 < δ := by linarith
  have hσpos : 0 < σ := by linarith
  have hσ1' : σ < 1 := by linarith
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by rw [abs_zero]; exact hT))
  have hmem : ∀ u ∈ Set.uIcc (-T) T, |u| ≤ T := by
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    exact abs_le.2 ⟨hu.1, hu.2⟩
  have hc : ∀ w : ℝ, 0 < w → IntervalIntegrable
      (fun u : ℝ => Formalism.ZeroFreeDirichlet.Fchi χ w ((σ : ℂ) + (u : ℂ) * I)) MeasureTheory.volume (-T) T := by
    intro w hw
    apply ContinuousOn.intervalIntegrable
    intro u hu
    exact (tc_cont χ hχ w σ u hw hσpos hσ1' (hL u (hmem u hu))).continuousWithinAt
  have hz1 : 0 < z + z * η := by nlinarith
  rw [← intervalIntegral.integral_sub (hc _ hz1) (hc _ hz)]
  have hK : 0 ≤ M * (4 * η * z ^ σ) := by positivity
  have hpt : ∀ u : ℝ, |u| ≤ T →
      ‖Formalism.ZeroFreeDirichlet.Fchi χ (z + z * η) ((σ : ℂ) + (u : ℂ) * I) - Formalism.ZeroFreeDirichlet.Fchi χ z ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        M * (4 * η * z ^ σ) * (2 / (δ + |u|)) := by
    intro u hu
    refine (tc_left_pt χ z η σ M hz hη hη1 hσpos hσ1' u (hM u hu)).trans ?_
    apply mul_le_mul_of_nonneg_left _ hK
    have hre : ((σ : ℂ) + (u : ℂ) * I - 1).re = σ - 1 := by simp
    have him : ((σ : ℂ) + (u : ℂ) * I - 1).im = u := by simp
    have h1 := Complex.abs_re_le_norm ((σ : ℂ) + (u : ℂ) * I - 1)
    rw [hre, abs_of_neg (by linarith)] at h1
    have h2 := Complex.abs_im_le_norm ((σ : ℂ) + (u : ℂ) * I - 1)
    rw [him] at h2
    have hpos : 0 < δ + |u| := by have := abs_nonneg u; linarith
    rw [div_le_div_iff₀ (by linarith) hpos]
    linarith
  have hgc : Continuous (fun u : ℝ => 2 / (δ + |u|)) :=
    continuous_const.div (by fun_prop)
      (fun u => (by have := abs_nonneg u; linarith : (0 : ℝ) < δ + |u|).ne')
  have hg : IntervalIntegrable (fun u : ℝ => M * (4 * η * z ^ σ) * (2 / (δ + |u|)))
      MeasureTheory.volume (-T) T :=
    (continuous_const.mul hgc).intervalIntegrable _ _
  refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_ hg).trans ?_
  · refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu' : -T < u ∧ u ≤ T := by
      first
        | exact hu
        | (rw [Set.uIoc_of_le (by linarith)] at hu; exact hu)
    exact hpt u (abs_le.2 ⟨hu'.1.le, hu'.2⟩)
  rw [intervalIntegral.integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ hK
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hgc.intervalIntegrable _ _)
    (hgc.intervalIntegrable _ _)]
  have hA : ∫ u in (-T)..0, 2 / (δ + |u|) = -2 * Real.log (δ - 0) - -2 * Real.log (δ - -T) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => -2 * Real.log (δ - u))
    · intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      have hpos : 0 < δ - x := by linarith [hx.2]
      have h := (((hasDerivAt_id x).const_sub δ).log hpos.ne').const_mul (-2)
      refine h.congr_deriv ?_
      rw [abs_of_nonpos hx.2]
      try simp only [id_eq]
      ring
    · exact hgc.intervalIntegrable _ _
  have hB : ∫ u in (0 : ℝ)..T, 2 / (δ + |u|) = 2 * Real.log (δ + T) - 2 * Real.log (δ + 0) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => 2 * Real.log (δ + u))
    · intro x hx
      rw [Set.uIcc_of_le hT] at hx
      have hpos : 0 < δ + x := by linarith [hx.1]
      have h := (((hasDerivAt_id x).const_add δ).log hpos.ne').const_mul 2
      refine h.congr_deriv ?_
      rw [abs_of_nonneg hx.1]
      try simp only [id_eq]
      ring
    · exact hgc.intervalIntegrable _ _
  rw [hA, hB]
  simp only [sub_zero, add_zero, sub_neg_eq_add]
  have hq : (δ + T) / δ ≤ 1 + 800 * T := by
    rw [div_le_iff₀ hδpos]
    nlinarith [mul_nonneg hT (by linarith : (0 : ℝ) ≤ 800 * δ - 1)]
  have hlog : Real.log (δ + T) - Real.log δ ≤ Real.log (1 + 800 * T) := by
    rw [← Real.log_div (by linarith) hδpos.ne']
    exact Real.log_le_log (div_pos (by linarith) hδpos) hq
  linarith
end Formalism.HermitianLattices.Ext.BoxTail
