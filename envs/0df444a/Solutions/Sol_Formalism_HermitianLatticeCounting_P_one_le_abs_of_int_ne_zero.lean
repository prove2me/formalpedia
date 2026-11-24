-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.one_le_abs_of_int_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:46.73886+00:00
-- url     : https://prove2.me/submissions/e66a934c-f8bd-4cc2-8d0e-554c0917e1bf

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
theorem _root_.solution (y : ℝ) (z : ℤ) (h : y = (z : ℝ)) (hy : y ≠ 0) : 1 ≤ |y| := by
  subst h
  have hz : z ≠ 0 := by
    intro h0
    apply hy
    simp [h0]
  exact_mod_cast Int.one_le_abs hz
end Formalism.HermitianLatticeCounting.P
