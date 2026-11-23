-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.level_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:20.40373+00:00
-- url     : https://prove2.me/submissions/7a90b1cf-6674-4f9e-a84f-6ab1082da104

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_notMem_Xa

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
theorem _root_.solution (F : FlagD H r) {x : V} {a : Fin r} {al : K} (h : F.HasLevel x a al) :
    x ∉ F.Xa a.val := by
  obtain ⟨hal, hx'⟩ := h
  intro hx
  have h1 : al • F.e a.castSucc ∈ F.Xa a.val := by
    simpa using Submodule.sub_mem _ hx hx'
  exact (e_notMem_Xa F) a ((Submodule.smul_mem_iff _ hal).1 h1)
end Formalism.HermitianLatticeCounting.P
