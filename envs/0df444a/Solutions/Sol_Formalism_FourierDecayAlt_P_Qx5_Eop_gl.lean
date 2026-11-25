-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.Eop_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:08:22.612925+00:00
-- url     : https://prove2.me/submissions/d6894c3a-dbfe-41d9-9bf4-effff4769154

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
theorem _root_.solution {E : Fin n → Fin n → A} (hE : GlRel E) : GlRel (Eop E) := by
  intro a b c d
  have h := hE d c b a
  simp only [Eop, neg_mul_neg]
  have h2 : E b a * E d c - E d c * E b a = -(E d c * E b a - E b a * E d c) := by abel
  rw [h2, h]
  have e1 : (c = b) = (b = c) := propext eq_comm
  have e2 : (a = d) = (d = a) := propext eq_comm
  simp only [e1, e2]
  by_cases h1 : b = c <;> by_cases h3 : d = a <;> (simp [h1, h3]; try abel)
end Formalism.FourierDecayAlt.P.Qx5
