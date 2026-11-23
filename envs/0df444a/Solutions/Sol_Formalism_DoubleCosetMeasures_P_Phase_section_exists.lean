-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.section_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:11.53911+00:00
-- url     : https://prove2.me/submissions/d6c7859a-338a-4c8f-9836-cbff4c0ad691

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_inj
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_lt_of_blk_eq
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_lt_of_blk_lt
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_lt_of_lt_of_ne
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_pt_mul_ptI
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_conj_apply
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_low_zero
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_up_zero
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_one_low
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_inv_mul_one_low
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_bdiag_low
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_blockDiag_apply_same_block
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
section
set_option maxHeartbeats 400000
noncomputable section
open Matrix
namespace Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
namespace Phase
variable {K : Type} [CommRing K]
private lemma isLowUni_mul' {n : ℕ} {x y : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x)
    (hy : IsLowUni y) : IsLowUni (x * y) := by
  have h1 : (x * y).IsLowerTriangular := Matrix.BlockTriangular.mul hx.1 hy.1
  unfold IsLowUni
  refine ⟨h1, fun a => ?_⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hx.2 a, hy.2 a, one_mul]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · rw [low_zero hy h, mul_zero]
    · rw [low_zero hx h, zero_mul]
  · simp
private lemma isLowUni_inv' {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x) :
    IsLowUni x⁻¹ := by
  have hd : IsUnit x.det := by
    rw [Matrix.det_of_isLowerTriangular x hx.1]
    simp [hx.2]
  letI := Matrix.invertibleOfIsUnitDet x hd
  have h1 : x⁻¹.IsLowerTriangular := Matrix.blockTriangular_inv_of_blockTriangular hx.1
  unfold IsLowUni
  refine ⟨h1, fun a => ?_⟩
  have h := congrFun (congrFun (mul_inv_one_low hx) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, hx.2 a, one_mul, Matrix.one_apply_eq] at h
  · exact h
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h' | h'
    · have hz : x⁻¹ b a = 0 := h1 (show OrderDual.toDual a < OrderDual.toDual b from h')
      rw [hz, mul_zero]
    · rw [low_zero hx h', zero_mul]
  · simp
private lemma isUpUni_mul' {n : ℕ} {x y : Matrix (Fin n) (Fin n) K} (hx : IsUpUni x)
    (hy : IsUpUni y) : IsUpUni (x * y) := by
  have h1 : (x * y).IsUpperTriangular := Matrix.BlockTriangular.mul hx.1 hy.1
  unfold IsUpUni
  refine ⟨h1, fun a => ?_⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hx.2 a, hy.2 a, one_mul]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · rw [up_zero hx h, zero_mul]
    · rw [up_zero hy h, mul_zero]
  · simp
private lemma bdiag_apply (s : List ℕ) (x : Matrix (Fin s.sum) (Fin s.sum) K)
    (a c : Fin s.sum) : bdiag s x a c = if blk s a = blk s c then x a c else 0 := rfl
end Phase
end Formalism.DoubleCosetMeasures.P
end
end

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
open Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K]
namespace Formalism.DoubleCosetMeasures.P.Phase
theorem _root_.solution (s : List ℕ) (t : ℕ → Kˣ) {x y : Matrix (Fin s.sum) (Fin s.sum) K}
    (hx : IsLowUni x) (hy : IsUpUni y) :
    ∃ v u h : Matrix (Fin s.sum) (Fin s.sum) K, IsLowUni v ∧ IsLowUni h ∧
      v * pt s t = pt s t * h ∧ IsUpUni u ∧ v * pt s t * u = x * pt s t * y := by
  have hv1 : IsLowUni (x * (bdiag s x)⁻¹) := isLowUni_mul' hx (isLowUni_inv' (bdiag_low s hx))
  have hW : IsUpUni (ptI s t * bdiag s x * pt s t) := by
    unfold IsUpUni
    constructor
    · intro a c hca
      have hca' : c < a := hca
      rw [conj_apply]
      have hw : bdiag s x (revF s a) (revF s c) = 0 := by
        rw [bdiag_apply]
        by_cases hb : blk s a = blk s c
        · rw [if_pos (show blk s (revF s a) = blk s (revF s c) by rw [blk_revF, blk_revF, hb]),
            low_zero hx (revF_lt_of_blk_eq s hb.symm hca')]
        · rw [if_neg (show ¬ blk s (revF s a) = blk s (revF s c) by
            rw [blk_revF, blk_revF]; exact hb)]
      rw [hw, mul_zero, zero_mul]
    · intro a
      rw [conj_apply, bdiag_apply, if_pos rfl, hx.2, mul_one, Units.inv_mul]
  refine ⟨x * (bdiag s x)⁻¹, ptI s t * bdiag s x * pt s t * y,
    ptI s t * (x * (bdiag s x)⁻¹) * pt s t, hv1, ?_, ?_, isUpUni_mul' hW hy, ?_⟩
  · unfold IsLowUni
    constructor
    · intro a c hac
      have hac' : a < c := hac
      rw [conj_apply]
      have hv : (x * (bdiag s x)⁻¹) (revF s a) (revF s c) = 0 := by
        by_cases hb : blk s a = blk s c
        · rw [mul_inv_blockDiag_apply_same_block s hx (a := revF s a) (c := revF s c) (by rw [blk_revF, blk_revF, hb]),
            Matrix.one_apply_ne (fun h' => (ne_of_lt hac') (revF_inj s h'))]
        · exact low_zero hv1 (revF_lt_of_blk_lt s (blk_lt_of_lt_of_ne s hac' hb))
      rw [hv, mul_zero, zero_mul]
    · intro a
      rw [conj_apply, mul_inv_blockDiag_apply_same_block s hx (a := revF s a) (c := revF s a) rfl, Matrix.one_apply_eq,
        mul_one, Units.inv_mul]
  · simp only [← Matrix.mul_assoc, pt_mul_ptI, Matrix.one_mul]
  · calc x * (bdiag s x)⁻¹ * pt s t * (ptI s t * bdiag s x * pt s t * y)
        = x * ((bdiag s x)⁻¹ * ((pt s t * ptI s t) * bdiag s x)) * pt s t * y := by
          simp only [Matrix.mul_assoc]
      _ = x * pt s t * y := by
          rw [pt_mul_ptI, Matrix.one_mul, inv_mul_one_low (bdiag_low s hx), Matrix.mul_one]
end Formalism.DoubleCosetMeasures.P.Phase
