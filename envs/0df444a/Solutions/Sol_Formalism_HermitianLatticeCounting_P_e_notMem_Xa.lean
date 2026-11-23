-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.e_notMem_Xa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:35.42658+00:00
-- url     : https://prove2.me/submissions/682d017a-af6a-49d7-8f0c-584642b6cc71

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
theorem _root_.solution (F : FlagD H r) (a : Fin r) : F.e a.castSucc ∉ F.Xa a.val := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  first
  | exact F.indep.notMem_span_image (s := {b : Fin r | b.val < a.val}) (by simp)
  | exact F.indep.not_mem_span_image (s := {b : Fin r | b.val < a.val}) (by simp)
end Formalism.HermitianLatticeCounting.P
