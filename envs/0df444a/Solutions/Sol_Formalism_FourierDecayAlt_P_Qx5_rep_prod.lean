-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.rep_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:55:07.612242+00:00
-- url     : https://prove2.me/submissions/5ce6d420-4a0c-4c24-a636-68b3a5d6975f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_Rep_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_rep_Tm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_top


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
theorem _root_.solution (hD : IsOpen D) (L : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i))) :
    Rep ((L.map fun p => Tm (Eh (E := E) hD) p.1 p.2.1 p.2.2).prod)
      (fun f => (L.map fun p => QuantumDeterminants.Top (EH k r) p.1 (posL k r i p.2.1) (posL k r i p.2.2)).foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact fun _ _ _ => rfl
  | cons p L ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons]
    exact (rep_Tm hD p.1 p.2.1 p.2.2).mul ih (good_top hD _ _ _)
end Formalism.FourierDecayAlt.P.Qx5
