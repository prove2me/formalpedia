-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.theorem_B_entry_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:27.024608+00:00
-- url     : https://prove2.me/submissions/f3a7c002-8ae1-4b33-9a4d-38aaf5ef8932

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ArithmeticLatticeHypothesis
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_TheoremBEntryFormula
import Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_P_JJ
import Theorems.Thm_Formalism_SLP_GlobalBoundRefinements_P_entry_MNinv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements
namespace Formalism.SLP.GlobalBoundRefinements.P
theorem _root_.solution : ThmBEntry := by
  intro M N sh₁ ch₁ sh₂ ch₂ hM hN hs₁ hc₁ hcs₁ hs₂ hc₂ hcs₂ hN10 hM10

  have hright : ∀ P : Matrix (Fin 2) (Fin 2) ℂ, P.conjTranspose * J * P = J →
      P * J * P.conjTranspose = J := by
    intro P hP
    have hl : (J * P.conjTranspose * J) * P = 1 := by
      calc J * P.conjTranspose * J * P = J * (P.conjTranspose * J * P) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hP, JJ]
    have hu := Matrix.isUnit_det_of_left_inverse hl
    have hr : P * (J * P.conjTranspose * J) = 1 := by
      rw [← Matrix.inv_eq_left_inv hl]
      exact Matrix.mul_nonsing_inv P hu
    calc P * J * P.conjTranspose = P * (J * P.conjTranspose * J) * J := by
          simp only [Matrix.mul_assoc, JJ, Matrix.mul_one]
      _ = J := by rw [hr, Matrix.one_mul]
  have hsq : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsq' : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [mul_comm, hsq]

  have hNc : ‖N 0 0‖ ^ 2 - ‖N 1 0‖ ^ 2 = 1 := by
    have h1 := congrFun (congrFun hN 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, J, Matrix.conjTranspose_apply] at h1
    rw [hsq', hsq'] at h1
    all_goals exact_mod_cast h1

  have hNr : ‖N 0 0‖ ^ 2 - ‖N 0 1‖ ^ 2 = 1 := by
    have h1 := congrFun (congrFun (hright N hN) 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, J, Matrix.conjTranspose_apply] at h1
    rw [hsq, hsq] at h1
    all_goals exact_mod_cast h1
  have hMr : ‖M 1 0‖ ^ 2 - ‖M 1 1‖ ^ 2 = -1 := by
    have h1 := congrFun (congrFun (hright M hM) 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, J, Matrix.conjTranspose_apply] at h1
    rw [hsq, hsq] at h1
    all_goals exact_mod_cast h1
  have h01 : ‖N 0 1‖ = 1 / sh₁ := by
    rw [← hN10]
    have : ‖N 0 1‖ ^ 2 = ‖N 1 0‖ ^ 2 := by linarith
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  have h00 : ‖N 0 0‖ = ch₁ / sh₁ := by
    have : ‖N 0 0‖ ^ 2 = (ch₁ / sh₁) ^ 2 := by
      rw [div_pow, hcs₁]
      have e : ‖N 0 0‖ ^ 2 = 1 + ‖N 1 0‖ ^ 2 := by linarith
      rw [e, hN10]
      field_simp
      all_goals ring
    exact (pow_left_inj₀ (norm_nonneg _) (div_nonneg hc₁ hs₁.le) two_ne_zero).mp this
  have h11 : ‖M 1 1‖ = ch₂ / sh₂ := by
    have : ‖M 1 1‖ ^ 2 = (ch₂ / sh₂) ^ 2 := by
      rw [div_pow, hcs₂]
      have e : ‖M 1 1‖ ^ 2 = 1 + ‖M 1 0‖ ^ 2 := by linarith
      rw [e, hM10]
      field_simp
      all_goals ring
    exact (pow_left_inj₀ (norm_nonneg _) (div_nonneg hc₂ hs₂.le) two_ne_zero).mp this
  rw [entry_MNinv M N hN]
  calc ‖M 1 0 * (starRingEnd ℂ) (N 0 0) - M 1 1 * (starRingEnd ℂ) (N 0 1)‖
      ≤ ‖M 1 0 * (starRingEnd ℂ) (N 0 0)‖ + ‖M 1 1 * (starRingEnd ℂ) (N 0 1)‖ := norm_sub_le _ _
    _ = ‖M 1 0‖ * ‖N 0 0‖ + ‖M 1 1‖ * ‖N 0 1‖ := by
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    _ = (ch₁ + ch₂) / (sh₁ * sh₂) := by
      rw [hM10, h00, h11, h01]
      field_simp
      all_goals ring
end Formalism.SLP.GlobalBoundRefinements.P
