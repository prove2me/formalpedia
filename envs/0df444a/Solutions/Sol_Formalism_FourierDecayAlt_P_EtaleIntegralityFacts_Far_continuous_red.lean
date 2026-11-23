-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far.continuous_red
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:50.725791+00:00
-- url     : https://prove2.me/submissions/2423a512-fe95-4694-8fe1-004df9874f3e

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_tri_cases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
theorem _root_.solution (m : ℕ) (y : UT (m + 2) → ℂ) :
    Continuous (fun x : Fin (m + 1) → ℂ => redOf m (x, y)) := by
  have h : ∀ i j, Continuous (fun x : Fin (m + 1) → ℂ => triXY x y i j) := by
    intro i j
    rcases tri_cases m i j with h | ⟨k, h⟩ | ⟨e, h⟩
    · simp only [h]; exact continuous_const
    · simp only [h]; exact continuous_apply k
    · simp only [h]; exact continuous_const
  unfold redOf
  exact Continuous.prodMk (h _ _) (Continuous.prodMk (continuous_pi fun k => h _ _)
    (Continuous.prodMk (continuous_pi fun q => h _ _) (continuous_pi fun i => h _ _)))
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
