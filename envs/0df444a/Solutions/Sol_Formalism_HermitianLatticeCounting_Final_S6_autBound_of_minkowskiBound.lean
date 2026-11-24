-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.autBound_of_minkowskiBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:32.501127+00:00
-- url     : https://prove2.me/submissions/55526495-e2d4-432a-b7ec-19e61cbb3785

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Formalism_FlagUnipotentLattices_AutBoundOfMinkowskiBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_S6_minkowskiDvdFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S6
namespace Formalism.HermitianLatticeCounting.Final.S6
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.MinkowskiBound → Formalism.HermitianLatticeCounting.S6.AutBound := by
  intro hMk s f G hG
  have h1 := (hMk (2 * s * f) G hG).trans (minkowskiDvdFactorial (2 * s * f))
  have h2 : Nat.card G ≤ (2 * (2 * s * f)).factorial := Nat.le_of_dvd (Nat.factorial_pos _) h1
  have h3 : (2 * (2 * s * f)).factorial ≤ (4 * s * f) ^ (4 * s * f) := by
    have e : 2 * (2 * s * f) = 4 * s * f := by ring
    rw [e]
    exact Nat.factorial_le_pow _
  exact_mod_cast h2.trans h3
end Formalism.HermitianLatticeCounting.Final.S6
