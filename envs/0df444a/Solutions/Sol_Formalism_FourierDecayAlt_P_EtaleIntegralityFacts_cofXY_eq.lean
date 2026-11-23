-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.cofXY_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:42.755501+00:00
-- url     : https://prove2.me/submissions/d228b79e-7dc7-4c9a-bfc4-8009623265c4

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_cofXY_def
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_top_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_sum_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Formalism.FourierDecayAlt.G Matrix
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
theorem _root_.solution (m : ℕ) (t : ℂ) (p : XY m) : cofXY m t p = cof0XY m p + t * cof1XY m t p := by
  rw [cofXY_def, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, top_eq,
    sum_shift m t (fun j => ((-Xm m p) ^ j *ᵥ Bm m p) 0), cof1XY, add_comm]
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
