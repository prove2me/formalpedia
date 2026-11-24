-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.automorphism_bound_of_hyp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:41.020817+00:00
-- url     : https://prove2.me/submissions/29ac4b27-c84f-45c9-a6e3-a364abf2c64d

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.AutBoundAsm := by
  intro hM hD s f G hG
  have h1 := (hM (2 * s * f) G hG).trans (hD (2 * s * f))
  have h2 := Nat.le_of_dvd (Nat.factorial_pos _) h1
  have h3 := h2.trans (Nat.factorial_le_pow _)
  have e : 2 * (2 * s * f) = 4 * s * f := by ring
  rw [e] at h3
  exact_mod_cast h3
end Formalism.HermitianLatticeCounting.P
