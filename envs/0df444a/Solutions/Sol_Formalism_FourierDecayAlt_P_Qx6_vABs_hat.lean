-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.vABs_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:41:53.861805+00:00
-- url     : https://prove2.me/submissions/10217d83-278b-4ac6-9423-80fbbbc9bd7e

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_good_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_good_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_good_TLs
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (H : HatData (Fn k r E))
variable {H}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hop : ∀ l q, H.Good (crd (opL l q))) (Y : ℂ) : ∀ (j : ℕ) (a : Fin 2),
    H.Good (crd (cmp (vABs (E := E) r Y j) a)) ∧ H.hat (crd (cmp (vABs (E := E) r Y j) a)) = Lp H Y j 0 a
  | 0, a => by
    fin_cases a
    · exact ⟨HatData.good_id, HatData.hat_id⟩
    · exact ⟨HatData.good_zero, HatData.hat_zero⟩
  | j + 1, a => by
    obtain ⟨gA, hA⟩ := solution hop Y j 0
    obtain ⟨gB, hB⟩ := solution hop Y j 1
    by_cases hj : j < r
    · have ev : vABs (E := E) r Y (j + 1) =
          (fun f => (vABs r Y j).1 (Y • f - pbOp ⟨j, hj⟩ f) - (vABs r Y j).2 (cbOp ⟨j, hj⟩ f),
            fun f => (vABs r Y j).1 (cbiOp ⟨j, hj⟩ f)) := by
        show (if h : j < r then _ else _) = _
        rw [dif_pos hj]
      have hL : Lp H Y (j + 1) = Lp H Y j * hatM H (TLs k ⟨j, hj⟩ Y) := by
        simp only [Lp, dif_pos hj]
      have gT := good_TLs hop ⟨j, hj⟩ Y
      rw [hL, ev]
      have key0 : H.Good (crd (cmp ((fun f => (vABs r Y j).1 (Y • f - pbOp ⟨j, hj⟩ f) - (vABs r Y j).2 (cbOp ⟨j, hj⟩ f),
            fun f => (vABs r Y j).1 (cbiOp ⟨j, hj⟩ f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 0)) ∧
          H.hat (crd (cmp ((fun f => (vABs r Y j).1 (Y • f - pbOp ⟨j, hj⟩ f) - (vABs r Y j).2 (cbOp ⟨j, hj⟩ f),
            fun f => (vABs r Y j).1 (cbiOp ⟨j, hj⟩ f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 0)) = (Lp H Y j * hatM H (TLs k ⟨j, hj⟩ Y)) 0 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two, ← hA, ← hB]
        have e : crd (cmp ((fun f => (vABs r Y j).1 (Y • f - pbOp ⟨j, hj⟩ f) - (vABs r Y j).2 (cbOp ⟨j, hj⟩ f),
            fun f => (vABs r Y j).1 (cbiOp ⟨j, hj⟩ f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 0) =
            fun Φ : Fn k r E => crd (cmp (vABs (E := E) r Y j) 0) (TLs k ⟨j, hj⟩ Y 0 0 Φ) -
              crd (cmp (vABs (E := E) r Y j) 1) (crd (opL ⟨j, hj⟩ 4) Φ) := rfl
        rw [e]
        refine ⟨(gA.comp (gT 0 0)).sub (gB.comp (hop _ 4)), ?_⟩
        have h10 : hatM H (TLs k ⟨j, hj⟩ Y) 1 0 = -H.hat (crd (opL ⟨j, hj⟩ 4)) := HatData.hat_neg (hop _ 4)
        rw [HatData.hat_sub (gA.comp (gT 0 0)) (gB.comp (hop _ 4)), HatData.hat_comp gA (gT 0 0),
          HatData.hat_comp gB (hop _ 4), h10, mul_neg, ← sub_eq_add_neg]
        rfl
      have key1 : H.Good (crd (cmp ((fun f => (vABs r Y j).1 (Y • f - pbOp ⟨j, hj⟩ f) - (vABs r Y j).2 (cbOp ⟨j, hj⟩ f),
            fun f => (vABs r Y j).1 (cbiOp ⟨j, hj⟩ f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 1)) ∧
          H.hat (crd (cmp ((fun f => (vABs r Y j).1 (Y • f - pbOp ⟨j, hj⟩ f) - (vABs r Y j).2 (cbOp ⟨j, hj⟩ f),
            fun f => (vABs r Y j).1 (cbiOp ⟨j, hj⟩ f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 1)) = (Lp H Y j * hatM H (TLs k ⟨j, hj⟩ Y)) 0 1 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two, ← hA, ← hB]
        have e : crd (cmp ((fun f => (vABs r Y j).1 (Y • f - pbOp ⟨j, hj⟩ f) - (vABs r Y j).2 (cbOp ⟨j, hj⟩ f),
            fun f => (vABs r Y j).1 (cbiOp ⟨j, hj⟩ f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 1) =
            fun Φ : Fn k r E => crd (cmp (vABs (E := E) r Y j) 0) (TLs k ⟨j, hj⟩ Y 0 1 Φ) := rfl
        rw [e]
        refine ⟨gA.comp (gT 0 1), ?_⟩
        have h11 : hatM H (TLs k ⟨j, hj⟩ Y) 1 1 = 0 := HatData.hat_zero
        rw [HatData.hat_comp gA (gT 0 1), h11, mul_zero, add_zero]
        rfl
      fin_cases a
      · exact key0
      · exact key1
    · have ev : vABs (E := E) r Y (j + 1) = vABs r Y j := by
        show (if h : j < r then _ else _) = _
        rw [dif_neg hj]
      have hL : Lp H Y (j + 1) = Lp H Y j := by
        simp only [Lp, dif_neg hj, Matrix.mul_one]
      rw [ev, hL]
      exact solution hop Y j a
end Formalism.FourierDecayAlt.P.Qx6
