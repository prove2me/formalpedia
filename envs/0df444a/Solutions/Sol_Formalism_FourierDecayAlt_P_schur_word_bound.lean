-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.schur_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:55:07.085819+00:00
-- url     : https://prove2.me/submissions/05ef1995-ba86-4c45-9486-e2bfd72c5e17

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RowNormSquareBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_schur_two_factor_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset SchurNormSquareBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.SchurWords := by
  classical
  intro H _ _ G _ La ι PP Wd _ _ T τ V P φ θ θ' N ε D hinj hco hφ hS hθ hN hD hV
  have := schur_two_factor_bound H G La ι PP T τ V P φ (fun p t => ∑ w, θ p w * N w t)
    (fun p t => ∑ w, θ' p w * N w t) ε hinj hco hφ hS
    (fun p t ht => ⟨sum_nonneg fun w _ => mul_nonneg ((hθ p).1 w) (hN w t ht),
      sum_nonneg fun w _ => mul_nonneg ((hθ p).2.2.1 w) (hN w t ht)⟩) hV
  refine this.trans (add_le_add le_rfl ?_)

  have key : ∀ (ϑ : Wd → ℝ), (∀ w, 0 ≤ ϑ w) → ∑ w, ϑ w = 1 →
      ∑ t ∈ T, ∑ w, ϑ w * N w t ≤ D := by
    intro ϑ h0 h1
    rw [sum_comm]
    calc ∑ w, ∑ t ∈ T, ϑ w * N w t = ∑ w, ϑ w * ∑ t ∈ T, N w t := by simp only [mul_sum]
      _ ≤ ∑ w, ϑ w * D := sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hD w) (h0 w)
      _ = D := by rw [← sum_mul, h1, one_mul]
  rw [mul_sum]
  calc ∑ p, ε * ∑ t ∈ T, ((∑ w, θ p w * N w t) + ∑ w, θ' p w * N w t) / 2
      ≤ ∑ _p : PP, ε * D := by
        refine sum_le_sum fun p _ => ?_
        have hε : 0 ≤ ε := by simpa using hS p ∅ (by simp)
        refine mul_le_mul_of_nonneg_left ?_ hε
        have k1 := key (θ p) (hθ p).1 (hθ p).2.1
        have k2 := key (θ' p) (hθ p).2.2.1 (hθ p).2.2.2
        rw [← sum_div, sum_add_distrib]
        linarith
    _ = (Fintype.card PP : ℝ) * ε * D := by simp [mul_assoc]
end Formalism.FourierDecayAlt.P
