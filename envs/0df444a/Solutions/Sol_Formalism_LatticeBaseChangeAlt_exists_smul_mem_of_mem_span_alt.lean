-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.exists_smul_mem_of_mem_span_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:35:28.850574+00:00
-- url     : https://prove2.me/submissions/3e50e6d5-7f7e-4c8a-bae2-3fccc062390c

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Lemmata_MiscLemmasO_Imports
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ExistsSmulMemOfMemSpan
import Theorems.Thm_Bl_DiscreteValuationQuotients_goal1
import Theorems.Thm_Bl_SecondBlockLemmaP_goal1
import Theorems.Thm_P2M_Bl_general_b_fact_second____goal1_4dd01fbd6af8
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
open Formalism Formalism.LatticeBaseChangeAlt
open Module
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution (O K V : Type) [CommRing O] [IsDomain O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (M : Submodule O V) (v : V) (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ c : O, c ≠ 0 ∧ c • v ∈ M := by
  first | exact Bl.SecondBlockLemmaP.goal1 .. | (apply Bl.SecondBlockLemmaP.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaP.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaP.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaP.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaP.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M v hv | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M v | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V | exact @Bl.SecondBlockLemmaP.goal1 O K | exact @Bl.SecondBlockLemmaP.goal1 O
end Formalism.LatticeBaseChangeAlt
