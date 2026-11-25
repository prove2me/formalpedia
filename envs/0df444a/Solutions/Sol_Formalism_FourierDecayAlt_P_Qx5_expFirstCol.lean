-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.expFirstCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:06:57.653202+00:00
-- url     : https://prove2.me/submissions/17278fd9-6c2b-4b77-85c5-60149f404744

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_intCast_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_firstColumnSplit_bijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_firstColumnSplit_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_firstColumnSplit_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sign_insert_perm


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
theorem _root_.solution (E : Fin n → Fin n → A) {t : ℕ} (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E a b u = ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (l : ℕ)) •
      (Tm E u (a l) (b 0) * qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (u - 1)) := by
  unfold qminor
  rw [(Fintype.sum_bijective _ (Qx6.firstColumnSplit_bijective t) _ _ (fun _ => rfl)).symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [List.ofFn_succ, List.prod_cons]
  simp only [Qx6.sign_insert_perm, Qx6.firstColumnSplit_zero, Qx6.firstColumnSplit_succ, Function.comp, Fin.val_zero, Fin.val_succ]
  have e1 : u - ((0 : ℕ) : ℂ) = u := by simp
  have e2 : ∀ i : Fin t, u - (((i : ℕ) + 1 : ℕ) : ℂ) = u - 1 - ((i : ℕ) : ℂ) := by
    intro i; push_cast; ring
  simp only [e1, e2, intCast_smul, mul_smul_comm, smul_smul]
  congr 1
  push_cast
  ring
end Formalism.FourierDecayAlt.P.Qx5
