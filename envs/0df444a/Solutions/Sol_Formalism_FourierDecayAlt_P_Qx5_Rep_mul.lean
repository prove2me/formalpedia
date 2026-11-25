-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.Rep.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:47:31.525419+00:00
-- url     : https://prove2.me/submissions/853b061f-cdd7-431e-8d55-6684b1926764

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
open Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx5
namespace Rep
theorem _root_.solution {X Y : Module.End ℂ (VS k r i D E)} {T U : (Mx k r → E) → Mx k r → E} (hX : Rep X T) (hY : Rep Y U)
    (hT : Good k r i D T) : Rep (X * Y) (fun f => T (U f)) := fun v g hg => by
  rw [Module.End.mul_apply, hX _ g hg]
  exact hT.loc _ _ (hY v) g hg
end Rep
end Formalism.FourierDecayAlt.P.Qx5
