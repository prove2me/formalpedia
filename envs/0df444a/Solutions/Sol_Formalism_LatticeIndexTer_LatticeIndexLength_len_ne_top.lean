-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexLength.len_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:46.517648+00:00
-- url     : https://prove2.me/submissions/4df6c08e-f7e5-4185-9e64-1a35a86f7745

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexLength_length_quot_ne_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
open scoped Pointwise
open Formalism.LatticeIndexTer.LatticeIndexLength
namespace Formalism.LatticeIndexTer.LatticeIndexLength
theorem _root_.solution {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup X] [Module O X] (P D : Submodule O X) (hP : P.FG) (d : O) (hd : d ≠ 0)
    (h : ∀ p ∈ P, d • p ∈ D) : Module.length O (P ⧸ D.comap P.subtype) ≠ ⊤ := by
  have : Module.Finite O P := Module.Finite.iff_fg.2 hP
  refine length_quot_ne_top d hd _ (fun m => ?_)
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]
  exact h m m.2
end Formalism.LatticeIndexTer.LatticeIndexLength
