-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.germ_of_rate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:44.719844+00:00
-- url     : https://prove2.me/submissions/a41e2eb2-4c99-4316-957a-3e5fb2a6c6a3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_wMat_det_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_cont_detM
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_aux

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.G3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.GermOfRate := by
  rintro ⟨C₁, C₂, h⟩
  refine ⟨max C₁ C₂, fun m β hβ => ⟨fun _ => 1, by simp, ?_⟩⟩
  intro A hA Kc hKc h0 K ε hε
  obtain ⟨Cst, hC⟩ := h m β hβ Kc hKc h0
  obtain ⟨d0, hd0, hd⟩ : ∃ d0 : ℝ, 0 < d0 ∧ ∀ D ∈ Kc, d0 ≤ ‖D‖ := by
    rcases Kc.eq_empty_or_nonempty with rfl | hne
    · exact ⟨1, one_pos, by simp⟩
    · obtain ⟨D0, hD0, hmin⟩ := hKc.exists_isMinOn hne continuous_norm.continuousOn
      exact ⟨‖D0‖, norm_pos_iff.mpr (fun h => h0 (h ▸ hD0)), fun D hD => hmin hD⟩
  have hw : 0 < ‖(wMat (m + 1)).det‖ := norm_pos_iff.mpr (wMat_det_ne _)
  obtain ⟨r0, hr0, hr⟩ : ∃ r0 : ℝ, 0 < r0 ∧ ∀ Z : Mat (m + 1 + 1), detM Z ∈ detSet (m + 1) Kc → r0 ≤ ‖Z‖ := by
    have hc := (cont_detM (m + 1 + 1)).continuousAt (x := 0)
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨r, hrpos, hr⟩ := hc (‖(wMat (m + 1)).det‖ * d0) (mul_pos hw hd0)
    refine ⟨r, hrpos, fun Z hZ => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have h1 := hr (x := Z) (by simpa [dist_eq_norm] using hlt)
    have h00 : detM (0 : Mat (m + 1 + 1)) = 0 := by
      unfold detM
      exact Matrix.det_zero
    rw [h00, dist_eq_norm, sub_zero] at h1
    obtain ⟨D, hD, hDe⟩ := hZ
    rw [← hDe, norm_mul] at h1
    have := hd D hD
    nlinarith
  have hs : (1 : ℝ) ≤ (m : ℝ) + 2 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hmax1 : (C₁ : ℝ) ≤ ((max C₁ C₂ : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
  have hC1nn : (0 : ℝ) ≤ (C₁ : ℝ) := Nat.cast_nonneg _
  have hA1 : (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 ≤ A := by
    refine le_trans ?_ hA
    have h2 : ((m : ℝ) + 2) ^ 2 ≤ ((m : ℝ) + 2) ^ 3 := pow_le_pow_right₀ hs (by norm_num)
    have h3 : (0 : ℝ) ≤ ((m : ℝ) + 2) ^ 2 := by positivity
    nlinarith
  have hA0 : 0 ≤ A := le_trans (by positivity) hA1
  set Mx : ℝ := max 1 (r0 ^ (-A)) with hMx
  have hMx0 : 0 < Mx := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨ε / (|Cst| * (|K| * Mx) + 1), by positivity, ?_⟩
  intro V _ _ _ Φ hΦ t c ht htδ hD
  have hb : DerivBound (max C₁ C₂ * (m + 2) ^ 2) (detSet (m + 1) Kc)
      (fun Z => (|K| * Mx) * min 1 (‖Z‖ ^ (-A))) Φ := by
    intro Z hZ
    obtain ⟨h1, h2⟩ := hΦ Z hZ
    refine ⟨h1, fun j hj => (h2 j hj).trans ?_⟩
    have hZr := hr Z hZ
    have ha0 : 0 ≤ ‖Z‖ ^ (-A) := Real.rpow_nonneg (norm_nonneg _) _
    have ha1 : ‖Z‖ ^ (-A) ≤ r0 ^ (-A) := Real.rpow_le_rpow_of_nonpos hr0 hZr (by linarith)
    have h3 := aux _ _ ha0 ha1
    calc K * ‖Z‖ ^ (-A) ≤ |K| * ‖Z‖ ^ (-A) := mul_le_mul_of_nonneg_right (le_abs_self K) ha0
      _ ≤ |K| * (Mx * min 1 (‖Z‖ ^ (-A))) := mul_le_mul_of_nonneg_left h3 (abs_nonneg K)
      _ = (|K| * Mx) * min 1 (‖Z‖ ^ (-A)) := by ring
  have := hC V Φ A (|K| * Mx) (max C₁ C₂ * (m + 2) ^ 2) hA1
    (Nat.mul_le_mul_right _ (le_max_right _ _)) hb t c ht hD
  refine this.trans ?_
  have hq : 0 ≤ |Cst| * (|K| * Mx) := by positivity
  have h5 : Cst * (|K| * Mx) * ‖t‖ ≤ |Cst| * (|K| * Mx) * ‖t‖ := by
    have : Cst * (|K| * Mx) ≤ |Cst| * (|K| * Mx) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  refine h5.trans ?_
  rw [lt_div_iff₀ (by positivity)] at htδ
  nlinarith [norm_nonneg t]
end Formalism.FourierDecayAlt.P
