-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.GoodMap.inN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:26.838037+00:00
-- url     : https://prove2.me/submissions/f543970f-5f90-4f35-bea1-abbe9b390508

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_isotropicSpan_le_jointSpan_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_isotropicSpan_le_jointSpan_right

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
namespace GoodMap
theorem _root_.solution (F F' : FlagD H r) {g : V →ₗ[K] V} (hg : GoodMap F F' g) : F.InN g ∧ F'.InN g := by
  obtain ⟨hiso, hbij, hfix, hmeet⟩ := id hg
  constructor
  · unfold Formalism.HermitianLatticeCounting.S6.FlagD.InN
    refine ⟨hiso, hbij, fun a => ?_, fun y hy => ?_⟩
    · rw [hfix _ (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left F F' ((Formalism.HermitianLatticeCounting.P.e_mem_X F) a)), sub_self]
      exact Submodule.zero_mem _
    · exact (Submodule.mem_inf.1 (hmeet y fun u hu =>
        (Formalism.HermitianLatticeCounting.P.perp_X F) hy u (Submodule.mem_inf.1 hu).1)).1
  · unfold Formalism.HermitianLatticeCounting.S6.FlagD.InN
    refine ⟨hiso, hbij, fun a => ?_, fun y hy => ?_⟩
    · rw [hfix _ (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right F F' ((Formalism.HermitianLatticeCounting.P.e_mem_X F') a)), sub_self]
      exact Submodule.zero_mem _
    · exact (Submodule.mem_inf.1 (hmeet y fun u hu =>
        (Formalism.HermitianLatticeCounting.P.perp_X F') hy u (Submodule.mem_inf.1 hu).2)).2
end GoodMap
end Formalism.HermitianLatticeCounting.P
