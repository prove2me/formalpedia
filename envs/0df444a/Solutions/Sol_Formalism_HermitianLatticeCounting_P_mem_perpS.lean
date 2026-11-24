-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.mem_perpS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:40.471646+00:00
-- url     : https://prove2.me/submissions/0172a3a8-08d2-4c15-8885-280938b56d5c

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
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (H : HermSpace K V) (S : Submodule K V) (v : V) :
    v ∈ perpS H S ↔ ∀ s ∈ S, H.B s v = 0 := Iff.rfl
end Formalism.HermitianLatticeCounting.P
