-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.succ_eq_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:37.698082+00:00
-- url     : https://prove2.me/submissions/1809455c-891c-4792-a76c-82619f55927b

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
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ}
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {r : ℕ} (a : Fin r) (h : a.val + 1 = r) : a.succ = Fin.last r := Fin.ext (by simpa using h)
end Formalism.HermitianLatticeCounting.P
