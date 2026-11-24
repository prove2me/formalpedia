-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x7.liftVec_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:03:30.579834+00:00
-- url     : https://prove2.me/submissions/aec40343-9f32-4610-9c16-7ddb49c2601e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x7
theorem _root_.solution (c : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' (c • y) = c • liftVec k 1 r' y := by
  ext i
  rw [Pi.smul_apply]
  unfold liftVec
  by_cases hi : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
  · rw [dif_pos hi, dif_pos hi, Pi.smul_apply]
  · rw [dif_neg hi, dif_neg hi, smul_zero]
end Formalism.FourierDecayAlt.P.B2x7
