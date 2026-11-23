-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.norm_dterm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:56.970811+00:00
-- url     : https://prove2.me/submissions/59980d1d-eca3-42a7-ab4d-a4ccb857eeb3

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Theorems.Thm_P2M_Formalism_FX_LFunctionPartialSum_norm_cpow_sub_le__cd1d42d75e80
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_dterm_zero
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_natCast_add_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.FX
open Formalism.FX.LFunctionPartialSum
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.FX.LFunctionPartialSum
theorem _root_.solution {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dterm χ s n‖ ≤ B * (‖s‖ * (n : ℝ) ^ (-s.re - 1)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dterm_zero, norm_zero]
    exact mul_nonneg hB0 (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · have hx : (0 : ℝ) < n := by exact_mod_cast hn
    have key := norm_cpow_sub_le' hx hs
    rw [← natCast_add_one_eq, Complex.ofReal_natCast] at key
    show ‖Ap χ n * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hB n) key (norm_nonneg _) hB0
end Formalism.FX.LFunctionPartialSum
