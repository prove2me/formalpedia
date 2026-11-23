-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.DB.pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:05.786529+00:00
-- url     : https://prove2.me/submissions/175c6a0a-b45f-4564-9ebb-912321a3ea4e

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_clm_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Formalism.FourierDecayAlt.G Matrix Filter Topology
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
namespace DB
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {f : E → ι → F} {u : E} {S P : ℝ}
    (h : ∀ i, DB q (fun v => f v i) u S P) (hP : 0 ≤ P) : DB q f u (Fintype.card ι * S) P := by
  have e : f = fun v => ∑ i ∈ (Finset.univ : Finset ι), (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) (f v i) := by
    funext v
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [e]
  have h1 : ∀ i ∈ (Finset.univ : Finset ι),
      DB q (fun v => (ContinuousLinearMap.single ℝ (fun _ : ι => F) i) (f v i)) u S P := by
    intro i _
    refine DB.clm_one _ ?_ (h i)
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    show ‖(Pi.single i x : ι → F)‖ ≤ ‖x‖
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  have h2 := DB.sum Finset.univ hP h1
  simpa using h2
end DB
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
