-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexLength.exists_smul_mem_of_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:27.479805+00:00
-- url     : https://prove2.me/submissions/ccaf5206-55f8-4669-b674-199775184e90

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
import Theorems.Thm_P2M_Bl_general_b_fact_second___goal1_ca370a2b430e


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
variable {O K X : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
namespace Formalism.LatticeIndexTer.LatticeIndexLength
theorem _root_.solution (B : Submodule O X) (hB : Submodule.span K (B : Set X) = ⊤)
    (x : X) : ∃ d : O, d ≠ 0 ∧ d • x ∈ B := by
  first | exact Bl.general_b_fact_second''.goal1 .. | (apply Bl.general_b_fact_second''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› B hB x | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› B hB | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› B | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X | exact @Bl.general_b_fact_second''.goal1 O K | exact @Bl.general_b_fact_second''.goal1 O
end Formalism.LatticeIndexTer.LatticeIndexLength
