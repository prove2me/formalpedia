-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.Xa_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:52.306366+00:00
-- url     : https://prove2.me/submissions/3a94a190-3f00-4379-9bfb-ea9fde0b7d7b

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
theorem _root_.solution (F : FlagD H r) (a : Fin r) :
    F.Xa (a.val + 1) = F.Xa a.val ⊔ K ∙ F.e a.castSucc := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  have hs : {b : Fin r | b.val < a.val + 1} = {b | b.val < a.val} ∪ {a} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
    omega
  rw [hs, Set.image_union, Submodule.span_union, Set.image_singleton]
end Formalism.HermitianLatticeCounting.P
