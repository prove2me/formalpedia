-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.newton_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:08.427977+00:00
-- url     : https://prove2.me/submissions/b9f6a68a-dc4a-4eaf-b729-cad015015175

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittHS
import Theorems.Thm_Formalism_IndefR_LocBrg_newton_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
local notation "vv" => (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
variable (u : L)
namespace Formalism.IndefR.LocBrg
theorem _root_.solution (h2 : vv (2 : L) = 1) (hu : vv (u - 1) < 1) (k : ℕ) :
    vv (newtonSq u k - 1) < 1 ∧ vv (newtonSq u k * newtonSq u k - u) ≤ vv (u - 1) ^ (k + 1) := by
  induction k with
  | zero =>
    refine ⟨by simp [newtonSq], ?_⟩
    show vv (1 * 1 - u) ≤ vv (u - 1) ^ (0 + 1)
    rw [one_mul, pow_one, Valuation.map_sub_swap]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨hx1, hsq, hdiff⟩ := newton_step u k ih1 h2
    have h4 : vv (4 * newtonSq u k ^ 2) = 1 := by
      rw [Valuation.map_mul, Valuation.map_pow, hx1, one_pow, mul_one,
        show (4 : L) = 2 * 2 by norm_num, Valuation.map_mul, h2, one_mul]
    have hlt : vv (u - 1) ^ (k + 1) < 1 := by
      first
      | exact pow_lt_one₀ zero_le' hu (Nat.succ_ne_zero k)
      | exact pow_lt_one' hu (Nat.succ_ne_zero k)
    constructor
    · have he : newtonSq u (k + 1) - 1 = (newtonSq u (k + 1) - newtonSq u k) + (newtonSq u k - 1) := by
        ring
      rw [he]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ih1)
      rw [hdiff]
      exact lt_of_le_of_lt ih2 hlt
    · rw [hsq, Valuation.map_div, Valuation.map_pow, h4, div_one]
      calc vv (newtonSq u k * newtonSq u k - u) ^ 2 ≤ (vv (u - 1) ^ (k + 1)) ^ 2 := by
            first
            | exact pow_le_pow_left' ih2 2
            | exact pow_le_pow_left₀ zero_le' ih2 2
        _ = vv (u - 1) ^ ((k + 1) * 2) := by rw [← pow_mul]
        _ ≤ vv (u - 1) ^ (k + 1 + 1) := by
            first
            | exact pow_le_pow_right_of_le_one' hu.le (by omega)
            | exact pow_le_pow_right_of_le_one₀ zero_le' hu.le (by omega)
end Formalism.IndefR.LocBrg
