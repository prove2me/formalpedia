-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.ntw_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:44.636658+00:00
-- url     : https://prove2.me/submissions/35df719a-a1da-4d1e-9e0e-c671d6f48cdf

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_ntw_eh

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
variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution (φ : E →L[ℂ] E') (u : ℂ) (a b : Fin (mdim k r i)) :
    Ntw k r i D φ (fun f => QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) f)
      (fun f => QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) f) := by
  intro f hf x hx
  simp only [QuantumDeterminants.Top]
  have e1 : EH k r (posL k r i a) (posL k r i b) (fun y => φ (f y)) x = φ (EH k r (posL k r i a) (posL k r i b) f x) :=
    ntw_eh φ a b f hf x hx
  rw [e1, map_add]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.Qx5
