-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.ntw_eh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:15:22.227301+00:00
-- url     : https://prove2.me/submissions/2a7a93c8-942a-4588-b120-c92df0080976

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_ntw_rd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart_lev


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
theorem _root_.solution (φ : E →L[ℂ] E') (a b : Fin (mdim k r i)) :
    Ntw k r i D φ (fun f => EH k r (posL k r i a) (posL k r i b) f)
      (fun f => EH k r (posL k r i a) (posL k r i b) f) := by
  intro f hf x hx
  show RdV _ _ x + Complex.I • RdV _ _ x = φ (RdV _ f x + Complex.I • RdV _ f x)
  have e1 : RdV (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) (fun y => φ (f y)) x = φ (RdV _ f x) :=
    ntw_rd φ (hpart_lev i a b).1 f hf x hx
  have e2 : RdV (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) (fun y => φ (f y)) x = φ (RdV _ f x) :=
    ntw_rd φ (hpart_lev i a b).2 f hf x hx
  rw [e1, e2, map_add, map_smul]
end Formalism.FourierDecayAlt.P.Qx5
