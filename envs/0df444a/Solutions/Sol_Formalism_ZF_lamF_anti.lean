-- Prove2me | solution 1 for Formalism.ZF.lamF_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:21.139718+00:00
-- url     : https://prove2.me/submissions/684dd75d-1d81-4647-8fa8-863950de93f9

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormLogDerivLeLamF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution {σ τ : ℝ} (hσ : 1 < σ) (h : σ ≤ τ) : lamF τ ≤ lamF σ := by
  have hs : ∀ x : ℝ, 1 < x → Summable fun n => ‖term ↗Λ (x : ℂ) n‖ := fun x hx =>
    summable_norm_iff.2 (LSeriesSummable_vonMangoldt (by simpa using hx))
  unfold lamF
  refine Summable.tsum_le_tsum (fun n => ?_) (hs τ (by linarith)) (hs σ hσ)
  rw [norm_term_eq, norm_term_eq]
  split_ifs with hn
  · rfl
  · simp only [ofReal_re]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hn1 h)
end Formalism.ZF
