-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.isAnisotropicOfPosDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:48.382102+00:00
-- url     : https://prove2.me/submissions/982a7868-c70e-40c9-ad6a-963f15b5f687

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.AnisoOfPosDef := by
  intro K V _ _ _ _ σ H r F hpos w hw hww
  by_contra hwI
  have := hpos w hw hwI
  rw [hww, map_zero, Complex.zero_re] at this
  exact lt_irrefl _ this
end Formalism.HermitianLatticeCounting.P
