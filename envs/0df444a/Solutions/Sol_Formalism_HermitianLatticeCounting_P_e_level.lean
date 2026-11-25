-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.e_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:09:04.423774+00:00
-- url     : https://prove2.me/submissions/0c934e29-6f05-44f8-95cc-3b810595a4fc

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
theorem _root_.solution (F : FlagD H r) (a : Fin r) : F.HasLevel (F.e a.castSucc) a 1 := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.HasLevel
  exact ⟨one_ne_zero, by simp⟩
end Formalism.HermitianLatticeCounting.P
