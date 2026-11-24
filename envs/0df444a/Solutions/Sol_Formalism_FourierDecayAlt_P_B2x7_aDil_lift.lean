-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x7.aDil_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:53:00.112232+00:00
-- url     : https://prove2.me/submissions/e576ea06-4fb4-42e5-b911-120a0a37a625

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_aDil_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_dgR_shift

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
theorem _root_.solution (t : ℝ) (y : Fin (2 * r' + k + 1) → ℂ) :
    aDil k (1 + r') t *ᵥ liftVec k 1 r' y = liftVec k 1 r' (aDil k r' t *ᵥ y) := by
  rw [aDil_eq, aDil_eq]
  ext i
  rw [Matrix.mulVec_diagonal]
  unfold liftVec
  by_cases hi : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
  · rw [dif_pos hi, dif_pos hi, Matrix.mulVec_diagonal, dgR_shift t i hi]
  · rw [dif_neg hi, dif_neg hi, mul_zero]
end Formalism.FourierDecayAlt.P.B2x7
