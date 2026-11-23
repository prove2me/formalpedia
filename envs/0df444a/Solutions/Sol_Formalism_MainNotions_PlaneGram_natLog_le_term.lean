-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.natLog_le_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:24.746139+00:00
-- url     : https://prove2.me/submissions/842dfee4-8783-4957-b0dc-fc91516b508a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (r a : ℕ) :
    (r : ℝ) * (Nat.log p a : ℝ) ≤ (if a = 0 then 0 else (r : ℝ) * Real.logb p ((a : ℝ) + r)) := by
  split_ifs with ha
  · rw [ha, Nat.log_zero_right]
    simp
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg r)
    have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ha)
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    rw [Real.le_logb_iff_rpow_le (by exact_mod_cast (by omega : 1 < p)) (by linarith),
      Real.rpow_natCast]
    have h2 : ((p ^ Nat.log p a : ℕ) : ℝ) ≤ a := by exact_mod_cast Nat.pow_log_le_self p ha
    push_cast at h2
    linarith
end Formalism.MainNotions.PlaneGram
