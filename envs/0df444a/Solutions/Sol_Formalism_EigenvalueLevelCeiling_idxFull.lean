-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.idxFull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:26:36.708652+00:00
-- url     : https://prove2.me/submissions/2aa1ea35-d246-4787-ae6f-a478f3d93d5a

import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ErrSum
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxFull
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxPsiGood
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OnExport
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OnLocal
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxMono
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxScaleIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.EigenvalueLevelCeiling
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : IdxFull := by
  unfold IdxFull
  intro K _ _ _ Z _ _ _ _ _ w M Th ThK hM hTh hThK _ σ hσ hsc E r h
  obtain ⟨hL, heq⟩ := idxScaleIn K Z w ⊤ M ThK hM hThK σ hσ
  have hmono := idxMono K Z w ⊤ M Th (sc σ ThK) hM hTh hL hsc
  rw [heq, finrank_top] at hmono
  have h2 : (lix w M ThK : ℝ) + (Module.finrank K Z : ℝ) * (Formalism.DivisionValues.vw w σ : ℝ) ≤ (lix w M Th : ℝ) := by
    exact_mod_cast hmono
  nlinarith
end Formalism.EigenvalueLevelCeiling
