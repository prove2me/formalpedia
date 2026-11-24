-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.half_integer_neg_le_neg_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:29.390951+00:00
-- url     : https://prove2.me/submissions/5db805ab-b050-4c87-ac67-0b4f77855988

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (y : ℝ) (z : ℤ) (h : y = (z : ℝ) + 1 / 2) (hy : y < 0) : y ≤ -(1 / 2) := by
  subst h
  have hz : z ≤ -1 := by
    by_contra hcon
    push_neg at hcon
    have h0 : (0:ℤ) ≤ z := by omega
    have : (0:ℝ) ≤ z := by exact_mod_cast h0
    linarith
  have : (z:ℝ) ≤ -1 := by exact_mod_cast hz
  linarith
end Formalism.HermitianLatticeCounting.P
