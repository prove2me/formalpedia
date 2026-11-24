-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.model_words_assemble
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:32.837862+00:00
-- url     : https://prove2.me/submissions/50b29118-2a2e-499d-9022-714ceb5259ae

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelWordsAssemble
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_site_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M
open Mx9
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.ModelWordsAssemble := by
  intro hW hLS hSO hCh hLC P hP l S _ _ w hw
  refine ⟨fun i hi => hW.1 ℂ (A P) S (QQlev P l i) (qC P) w (hLS P hP l i hi) hw, ?_, ?_⟩
  · intro i
    have hσ := ((hSO P l).1 (siteA P i) (site_mem P i))
    refine hW.2.1 ℂ (A P) S (siteA P i) (QQlev P l (i + 1)) (QQlev P l i) w hσ.1 (hLC P l i) ?_ hw
    intro Y hY
    have h := (hCh P l).2 i Y
    rw [hY] at h
    exact h
  · intro Y hY hs z
    exact hW.2.2.2.1 ℂ (A P) S _ _ w Y (hSO P l) hw hY hs z
end Formalism.FourierDecayAlt.P
