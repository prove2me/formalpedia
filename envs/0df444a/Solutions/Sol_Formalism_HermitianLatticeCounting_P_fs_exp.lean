-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.fs_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:48.326489+00:00
-- url     : https://prove2.me/submissions/96ae5d91-2d2f-47be-a593-a7b6d64558df

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (j k f : ℕ) (hj1 : 1 ≤ j) (hjk : j + 2 ≤ k) : (k - 2) * f ≤ j * (k - 1 - j) * f := by
  apply Nat.mul_le_mul_right
  obtain ⟨t, rfl⟩ : ∃ t, k = j + 2 + t := ⟨k - (j + 2), by omega⟩
  have e1 : j + 2 + t - 1 - j = t + 1 := by omega
  have e2 : j + 2 + t - 2 = j + t := by omega
  rw [e1, e2]
  calc j + t ≤ j + j * t := Nat.add_le_add_left (Nat.le_mul_of_pos_left t hj1) j
    _ = j * (t + 1) := by ring
end Formalism.HermitianLatticeCounting.P
