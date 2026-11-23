-- Prove2me | solution 1 for Bl.general_b_fact_right_side.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:28.025863+00:00
-- url     : https://prove2.me/submissions/048024e0-4c78-463c-a847-dc464781c997

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_right_side
namespace Bl.general_b_fact_right_side
theorem _root_.solution :
  ∀ (x : Real),
  Iff
    (Eq.{1}
      (Complex.exp
        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (Complex.ofReal Real.pi)) Complex.I)
          (Complex.ofReal x)))
      1)
    (Exists.{1} fun (n : Int) ↦ Eq.{1} x (Int.cast.{0} n)) := by
  intro x
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h3 : (x : ℂ) = (n : ℂ) := by
      rw [mul_comm (n : ℂ)] at hn
      exact mul_left_cancel₀ h2 hn
    exact_mod_cast h3
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩
end Bl.general_b_fact_right_side
