-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.lix_locP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:53.35335+00:00
-- url     : https://prove2.me/submissions/50a4d005-64fd-4a0a-9250-876f17c42405

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementLoc
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_lidx_locP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] (w : HeightOneSpectrum (𝓞 K))
    (A B : Submodule (𝓞 K) Z) :
    lix w A B = lix w (localization₂ w.asIdeal A) (localization₂ w.asIdeal B) := by
  unfold lix
  exact lidx_locP _ A B
end Formalism.EigenvalueLevelCeiling
