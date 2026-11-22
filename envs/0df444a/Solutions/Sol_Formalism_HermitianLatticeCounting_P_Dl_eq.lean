-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.Dl_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:15.395949+00:00
-- url     : https://prove2.me/submissions/0748d0e2-3c78-48fc-a121-4fc78c261f4d

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
  {H : HermSpace K V} {r : ℕ}
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (F F' : FlagD H r) (l : ℕ) (hl : l ≤ r + 1) :
    Dl F F' l hl = (Matrix.of fun a b : Fin l => H.B (F.e (Fin.castLE hl a)) (F'.e (Fin.castLE hl b))).det := rfl
end Formalism.HermitianLatticeCounting.P
