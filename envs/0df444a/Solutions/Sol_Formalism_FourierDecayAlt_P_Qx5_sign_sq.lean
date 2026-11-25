-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.sign_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:54:21.450604+00:00
-- url     : https://prove2.me/submissions/6fb72fce-6c1e-4893-bd65-8f10b19500a0

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution (τ : Equiv.Perm (Fin n)) (X : A) :
    ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign τ : ℤ) : A) * X) = X := by
  rw [← mul_assoc, ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one, one_mul]
end Formalism.FourierDecayAlt.P.Qx5
