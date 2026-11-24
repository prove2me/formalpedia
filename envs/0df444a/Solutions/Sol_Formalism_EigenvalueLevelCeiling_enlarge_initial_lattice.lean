-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.enlarge_initial_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:56:16.155198+00:00
-- url     : https://prove2.me/submissions/b89fb5f0-6c1c-4428-a980-47006b355322

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxCutLe
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxMono


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
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : EnlargeInitialLattice := by
  intro K _ _ _ Z _ _ _ _ _ w M Th1 Th hM h1 hT h1T hTM E r h W
  have a := (idxCutLe K Z w ⊤ W M Th hM hT hTM le_top).1
  have b := (idxCutLe K Z w ⊤ W Th Th1 hT h1 h1T le_top).1
  have c := (idxCutLe K Z w ⊤ W Th1 Th1 h1 h1 le_rfl le_top).1
  have d : cut W Th1 ≤ cut W Th := inf_le_inf_right _ h1T
  have e := idxMono K Z w W (cut W M) (cut W Th1) (cut W Th) a c b d
  have e' : (lix w (cut W M) (cut W Th) : ℝ) ≤ (lix w (cut W M) (cut W Th1) : ℝ) := by exact_mod_cast e
  exact le_trans e' (h W)
end Formalism.EigenvalueLevelCeiling
