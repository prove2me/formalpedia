-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationWordBounds.orbital_derivative_words_weak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:30.443708+00:00
-- url     : https://prove2.me/submissions/f86d85e9-e6bc-4a96-9861-b32cbfbd4fb6

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalMeasurabilityWeakThreshold
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Asm_scalar_majorant_weak_threshold
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs2_domination_of_scalar_majorant
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs3_orbital_measurability_weak_threshold
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_SandwichRhoAction_dLR_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_continuous_xiP
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_norm_xiP
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationWordBounds_ck_all
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationWordBounds_words_all


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationWordBounds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
  Formalism.FourierDecayAlt.P.LetterPairRecursion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.WeakDominationWordBounds
theorem _root_.solution : Formalism.FourierDecayAlt.P.WeakThresholdClauses.JWordsW := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC
  have hDom1 := Formalism.FourierDecayAlt.P.JFxDs3.orbital_measurability_weak_threshold k r Wp Wq D A m F hThr hCC
  have hDom2 := Formalism.FourierDecayAlt.P.JFxDs2.domination_of_scalar_majorant Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.scalar_majorant_weak_threshold k r Wp Wq D A m F hThr hCC
  obtain ⟨c, hc⟩ := hCC
  have hFm : CkOn (m : ℕ∞) (GV k r) F := hc.1
  have hW := words_all D hFm hDom1 hDom2
  refine ⟨ck_all D hFm hDom1 hDom2, fun u v hu hv hl g hg => ?_⟩
  obtain ⟨bd, hbdI, hbd⟩ := hDom2 {g} isCompact_singleton (Set.singleton_subset_iff.2 hg)
  have hb := hbd u v hu hv hl g (Set.mem_singleton g)
  refine ⟨hbdI.norm.mono' ((continuous_xiP D).aestronglyMeasurable.smul (hDom1 u v hu hv hl g hg)) ?_, ?_⟩
  · filter_upwards [hb] with p hp
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_xiP D p)).trans (hp.trans (Real.le_norm_self _))
  · rw [hW u v hu hv hl g hg]
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS D] with p hp
    rw [dLR_rho D hp]
end Formalism.FourierDecayAlt.P.WeakDominationWordBounds
