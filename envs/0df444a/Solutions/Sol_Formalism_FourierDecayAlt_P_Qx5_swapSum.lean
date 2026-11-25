-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.swapSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:27:40.440072+00:00
-- url     : https://prove2.me/submissions/f3b5a73c-239c-493c-9ac5-b7f6a3b02946

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
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution {M : Type*} [AddCommMonoid M] {t : ℕ} (F : Fin (t + 1) → Fin t → M) :
    ∑ l, ∑ p, F l p = ∑ p : Fin (t + 1), ∑ l : Fin t, F (p.succAbove l) (l.predAbove p) := by
  let e : Fin (t + 1) × Fin t → Fin (t + 1) × Fin t := fun x => (x.1.succAbove x.2, x.2.predAbove x.1)
  have he : Function.Involutive e := by
    rintro ⟨p, l⟩
    simp only [e, Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]
  rw [← Fintype.sum_prod_type' F, ← Fintype.sum_prod_type' fun (p : Fin (t + 1)) (l : Fin t) => F (p.succAbove l) (l.predAbove p)]
  exact (Equiv.sum_comp he.toPerm fun x : Fin (t + 1) × Fin t => F x.1 x.2).symm
end Formalism.FourierDecayAlt.P.Qx5
