-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.capAdInv_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:53.31612+00:00
-- url     : https://prove2.me/submissions/3f248a03-3e5e-4902-8324-94c81428b0bb

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_gv_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_EHc_eq_LT
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_expandM
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_qm_eq__9adcf75d7042
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_skewRow
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_row_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_col_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_sum_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_det_sum
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_det_sum__d17b9508e216
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_qm_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_skewCol
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
theorem _root_.solution (y : Mat k r) (hy : y ∈ GV k r) (u : ℂ) (f : Mat k r → E) (h : Mat k r) (hh : h ∈ GV k r)
    (hloc : Loc ((Q.mdim k r 0 : ℕ) : ℕ∞) f h) :
    qminorOp (Formalism.FourierDecayAlt.P.JFxB.EHc k r y) (Q.posL k r 0) (Q.posL k r 0) u f h =
      qminorOp (Q.EH k r) (Q.posL k r 0) (Q.posL k r 0) u f h := by
  have hn : Q.mdim k r 0 = 2 * r + k + 1 := by unfold Q.mdim; simp
  let e : Fin (Q.mdim k r 0) ≃ Fin (2 * r + k + 1) := finCongr hn
  have hP : Q.posL k r 0 = ⇑e := by funext j; ext; simp [Q.posL, e]
  rw [hP, EHc_eq_LT y hy, qm_eq' (Mc y)]
  have h1 : ∀ σ : Equiv.Perm (Fin (Q.mdim k r 0)),
      fold (Mc y) (List.ofFn fun j : Fin (Q.mdim k r 0) => (u - ((j : ℕ) : ℂ), e (σ j), e j)) f h =
        ∑ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1),
          (∏ j, ((y⁻¹) (c j) (e (σ j)) * y (e j) (d j))) •
            fold (Msg k r) (List.ofFn fun j => (u - ((j : ℕ) : ℂ), c j, d j)) f h :=
    fun σ => expandM y hy _ _ f h hh hloc
  simp only [h1]
  have hA : ∀ σ : Equiv.Perm (Fin (Q.mdim k r 0)),
      (∑ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1),
        (∏ j, ((y⁻¹) (c j) (e (σ j)) * y (e j) (d j))) •
          fold (Msg k r) (List.ofFn fun j => (u - ((j : ℕ) : ℂ), c j, d j)) f h) =
      ∑ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1),
        ((∏ j, (y⁻¹) (c j) (e j)) * ∏ j, y (e j) (d j)) • FourTermExpansion.PP c d u σ f h := by
    intro σ
    rw [← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin (2 * r + k + 1))))]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    have hp : ∏ j, (y⁻¹) (c (σ j)) (e (σ j)) = ∏ j, (y⁻¹) (c j) (e j) :=
      Equiv.prod_comp σ (fun i => (y⁻¹) (c i) (e i))
    simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.id_comp, Function.comp_apply,
      id_eq, Finset.prod_mul_distrib, hp]
    rfl
  simp only [hA]
  rw [show (∑ σ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ∑ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1),
        ((∏ j, (y⁻¹) (c j) (e j)) * ∏ j, y (e j) (d j)) • FourTermExpansion.PP c d u σ f h) =
      ∑ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1), ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1),
        ((∏ j, (y⁻¹) (c j) (e j)) * ∏ j, y (e j) (d j)) • qminorOp (Q.EH k r) c d u f h by
    simp only [FourTermExpansion.qm_eq, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    ring]
  have hC : ∀ c : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1),
      ∑ d : Fin (Q.mdim k r 0) → Fin (2 * r + k + 1),
        ((∏ j, (y⁻¹) (c j) (e j)) * ∏ j, y (e j) (d j)) • qminorOp (Q.EH k r) c d u f h =
      ∑ τ : Equiv.Perm (Fin (Q.mdim k r 0)),
        ((∏ j, (y⁻¹) (c j) (e j)) * ∏ j, y (e j) ((e ∘ τ) j)) • qminorOp (Q.EH k r) c (e ∘ τ) u f h :=
    fun c => sum_inj e _ (fun d hd => by rw [col_zero c d u f h hh hloc hd, smul_zero])
  simp only [hC]
  rw [sum_inj e _ (fun c hc => Finset.sum_eq_zero fun τ _ => by rw [row_zero c _ u f h hc, smul_zero])]
  simp only [skewRow, FourTermExpansion.skewCol (⇑e) u f h hh hloc]
  have hdet : (∑ ρ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∏ j, (y⁻¹) (e (ρ j)) (e j)) *
      (∑ τ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ j, y (e j) (e (τ j))) = 1 := by
    rw [det_sum e, det_sum' e, ← Matrix.det_mul, (gv_inv hy).2, Matrix.det_one]
  calc _ = ((∑ ρ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∏ j, (y⁻¹) (e (ρ j)) (e j)) *
      (∑ τ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ j, y (e j) (e (τ j)))) •
        qminorOp (Q.EH k r) (⇑e) (⇑e) u f h := by
        rw [Finset.sum_mul_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp only [Function.comp_apply, smul_smul]
        congr 1
        ring
    _ = _ := by rw [hdet, one_smul]
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
