-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.vAB_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:24:47.583907+00:00
-- url     : https://prove2.me/submissions/e24a97f6-8a26-4e20-a082-60cdfd9ccb21

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_good_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_good_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_hat_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_good_TL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
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
theorem _root_.solution (hop : ∀ l q, H.Good (crd (opL l q))) (Y : ℂ) : ∀ (j : ℕ) (b : Fin 2),
    H.Good (crd (cmp (vAB (E := E) r Y j) b)) ∧ H.hat (crd (cmp (vAB (E := E) r Y j) b)) = Rp H Y j b 0
  | 0, b => by
    fin_cases b
    · exact ⟨HatData.good_id, HatData.hat_id⟩
    · exact ⟨HatData.good_zero, HatData.hat_zero⟩
  | j + 1, b => by
    obtain ⟨gA, hA⟩ := solution hop Y j 0
    obtain ⟨gB, hB⟩ := solution hop Y j 1
    by_cases hj : j < r
    · have ev : vAB (E := E) r Y (j + 1) =
          (fun f => Y • (vAB r Y j).1 f + pOp ⟨j, hj⟩ ((vAB r Y j).1 f) - cOp ⟨j, hj⟩ ((vAB r Y j).2 f),
            fun f => ciOp ⟨j, hj⟩ ((vAB r Y j).1 f)) := by
        show (if h : j < r then _ else _) = _
        rw [dif_pos hj]
      have hR : Rp H Y (j + 1) = hatM H (TL k ⟨j, hj⟩ Y) * Rp H Y j := by
        simp only [Rp, dif_pos hj]
      have gT := good_TL hop ⟨j, hj⟩ Y
      rw [hR, ev]
      have key0 : H.Good (crd (cmp ((fun f => Y • (vAB r Y j).1 f + pOp ⟨j, hj⟩ ((vAB r Y j).1 f) -
            cOp ⟨j, hj⟩ ((vAB r Y j).2 f), fun f => ciOp ⟨j, hj⟩ ((vAB r Y j).1 f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 0)) ∧
          H.hat (crd (cmp ((fun f => Y • (vAB r Y j).1 f + pOp ⟨j, hj⟩ ((vAB r Y j).1 f) -
            cOp ⟨j, hj⟩ ((vAB r Y j).2 f), fun f => ciOp ⟨j, hj⟩ ((vAB r Y j).1 f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 0)) =
            (hatM H (TL k ⟨j, hj⟩ Y) * Rp H Y j) 0 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two, ← hA, ← hB]
        have e : crd (cmp ((fun f => Y • (vAB r Y j).1 f + pOp ⟨j, hj⟩ ((vAB r Y j).1 f) -
            cOp ⟨j, hj⟩ ((vAB r Y j).2 f), fun f => ciOp ⟨j, hj⟩ ((vAB r Y j).1 f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 0) =
            fun Φ : Fn k r E => TL k ⟨j, hj⟩ Y 0 0 (crd (cmp (vAB (E := E) r Y j) 0) Φ) +
              TL k ⟨j, hj⟩ Y 0 1 (crd (cmp (vAB (E := E) r Y j) 1) Φ) := by
          funext Φ c g
          exact sub_eq_add_neg _ _
        rw [e]
        exact ⟨((gT 0 0).comp gA).add ((gT 0 1).comp gB), by
          rw [HatData.hat_add ((gT 0 0).comp gA) ((gT 0 1).comp gB), HatData.hat_comp (gT 0 0) gA,
            HatData.hat_comp (gT 0 1) gB]
          rfl⟩
      have key1 : H.Good (crd (cmp ((fun f => Y • (vAB r Y j).1 f + pOp ⟨j, hj⟩ ((vAB r Y j).1 f) -
            cOp ⟨j, hj⟩ ((vAB r Y j).2 f), fun f => ciOp ⟨j, hj⟩ ((vAB r Y j).1 f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 1)) ∧
          H.hat (crd (cmp ((fun f => Y • (vAB r Y j).1 f + pOp ⟨j, hj⟩ ((vAB r Y j).1 f) -
            cOp ⟨j, hj⟩ ((vAB r Y j).2 f), fun f => ciOp ⟨j, hj⟩ ((vAB r Y j).1 f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 1)) =
            (hatM H (TL k ⟨j, hj⟩ Y) * Rp H Y j) 1 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two, ← hA, ← hB]
        have e : crd (cmp ((fun f => Y • (vAB r Y j).1 f + pOp ⟨j, hj⟩ ((vAB r Y j).1 f) -
            cOp ⟨j, hj⟩ ((vAB r Y j).2 f), fun f => ciOp ⟨j, hj⟩ ((vAB r Y j).1 f)) :
              (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)) 1) =
            fun Φ : Fn k r E => TL k ⟨j, hj⟩ Y 1 0 (crd (cmp (vAB (E := E) r Y j) 0) Φ) := rfl
        rw [e]
        refine ⟨(gT 1 0).comp gA, ?_⟩
        have h11 : hatM H (TL k ⟨j, hj⟩ Y) 1 1 = 0 := HatData.hat_zero
        rw [HatData.hat_comp (gT 1 0) gA, h11, zero_mul, add_zero]
        rfl
      fin_cases b
      · exact key0
      · exact key1
    · have ev : vAB (E := E) r Y (j + 1) = vAB r Y j := by
        show (if h : j < r then _ else _) = _
        rw [dif_neg hj]
      have hR : Rp H Y (j + 1) = Rp H Y j := by
        simp only [Rp, dif_neg hj, Matrix.one_mul]
      rw [ev, hR]
      exact solution hop Y j b
end Formalism.FourierDecayAlt.P.Qx6
