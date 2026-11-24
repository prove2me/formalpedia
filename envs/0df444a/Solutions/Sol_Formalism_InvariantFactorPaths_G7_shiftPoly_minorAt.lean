-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.shiftPoly_minorAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:26.523083+00:00
-- url     : https://prove2.me/submissions/30cee6d0-7c63-4325-b1c5-04d61a0d5f3c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (jetPair)
variable {K σ κ : Type} [Field K] [DecidableEq σ] [Fintype κ]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {r0 r1 l : ℕ} (b : κ → σ × Fin r0 × Fin r1 → K) (s : σ)
    (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1) :
    shiftPoly b (minorAt s T I) = (Matrix.of fun (i c : Fin l) =>
      ∑ a, MvPolynomial.C (MvPolynomial.C (T i a)) * shiftGen b (s, a, I c)).det := by
  rw [shiftPoly_eq, minorAt, AlgHom.map_det]
  congr 1
  refine Matrix.ext fun i c => ?_
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [← shiftPoly_eq, shiftPoly_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [shiftPoly_mul, shiftPoly_C, shiftPoly_X]
end Formalism.InvariantFactorPaths.G7
