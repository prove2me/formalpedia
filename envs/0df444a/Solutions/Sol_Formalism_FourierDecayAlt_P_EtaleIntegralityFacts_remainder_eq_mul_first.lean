-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.remainder_eq_mul_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:32.511162+00:00
-- url     : https://prove2.me/submissions/5841aab6-1697-4c98-ae5c-d149157712bb

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Xm_strict
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_sum_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_isStrictUpper_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_pow_mulVec_succ


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
theorem _root_.solution (m : ℕ) (t : ℂ) (p : XY m) : R0 (Xm m p) (Bm m p) (rm m p) t = t * r1XY m t p := by
  rw [R0, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one,
    sum_shift m t (fun j => ∑ k : Fin m, rm m p k * ((-Xm m p) ^ j *ᵥ Bm m p) k.succ), r1XY]
  rw [Finset.sum_eq_zero (s := Finset.univ), add_zero]
  intro k _
  rw [G6.pow_mulVec_succ (G6.isStrictUpper_neg (Xm_strict m p)), mul_zero]
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
