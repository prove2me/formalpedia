-- Prove2me | solution 1 for Formalism.IndefR.Eqv.G5.fdom_exists_all
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:00.715391+00:00
-- url     : https://prove2.me/submissions/6a21ee53-2ec7-4b47-837c-b63bc46019ef

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasB_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_FdomExistsAll
import Theorems.Thm_Bl_SecondBlockLemmaC_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open Formalism Formalism.IndefR Formalism.IndefR.Eqv Formalism.IndefR.Eqv.G5
namespace Formalism.IndefR.Eqv.G5
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ s : Set G, MeasurableSet s ∧ ∀ μ : Measure G, IsFundamentalDomain Γ s μ := by
  first | exact Bl.SecondBlockLemmaC.goal1 .. | (apply Bl.SecondBlockLemmaC.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaC.goal1 <;> assumption)
end Formalism.IndefR.Eqv.G5
