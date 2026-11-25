-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.plane_exponential_bound_of_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:03:46.934297+00:00
-- url     : https://prove2.me/submissions/e4e13c66-e329-4151-9f33-ec4078b612b9

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_combine
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_decay
import Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_baseGram_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Finset Formalism.FourierDecayAlt
noncomputable section
open Formalism.FourierDecayAlt.P.JCx1.decay
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JC.PlaneExponentialBoundOfPlaces := by
  intro hGP hWP E _ _ _ Wp Wq _ _ _ _ S abelian₂ hPos hGr hWave hThr ε hε i hi1 hir w hw hcnt
  have hG : S.base.GramPSD := hGP E Wp Wq S hPos hGr _ _ _ _
  have hW : S.base.WordsPos := hWP E Wp Wq S hGr _ _ _ _
  obtain ⟨θ, hθ, hb⟩ := hWave ε hε i hi1 hir w hw hcnt
  refine ⟨θ, hθ, ?_⟩
  intro Y hY κ hκ l hl hl0
  have key := hb Y hY κ hκ l hl hl0 (S.bigPlaces i l)
  have hM : 0 ≤ ∑ w' ∈ S.base.Wb (S.base.cnt w + C.Kst), θ (S.bigPlaces i l) w' * S.base.N0 ε (i - 1) w' Y κ :=
    Finset.sum_nonneg fun w' _ => mul_nonneg ((hθ _).1 w') (BaseGramNonnegativity.baseGram_nonneg _ hG hW hε _ _ Y κ hκ)
  have hav : ∀ v, 0 < S.base.av v l := fun v => by
    show 0 < S.pl v l
    exact (S.pl v).pos_iff.mpr hl0
  exact combine C.Kst (abelian₂ i) (S.base.szD i) (fun v => S.base.av v l) _ _ _ (fun v => by simp [C.HidaSetting.bigPlaces]; rfl) (fun v => (hThr i hi1 hir v).1)
    (fun v => (hThr i hi1 hir v).2) hav hM key
end Formalism.FourierDecayAlt.P
