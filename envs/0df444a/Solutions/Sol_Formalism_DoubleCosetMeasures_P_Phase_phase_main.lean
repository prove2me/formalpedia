-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.phase_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:39.360798+00:00
-- url     : https://prove2.me/submissions/c89fce97-f437-4a96-bd23-a3c4658a6870

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_mono
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revIn_succ
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_lt_of_blk_lt
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_ptI_mul_pt
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_conj_apply
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_low_zero
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_up_zero
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_one_up
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_simple_add_zero
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
private lemma isUpUni_inv_lower_unipotent_orbits {n : ℕ} {x : Matrix (Fin n) (Fin n) K} (hx : IsUpUni x) :
    IsUpUni x⁻¹ := by
  have hd : IsUnit x.det := by
    rw [Matrix.det_of_isUpperTriangular hx.1]
    simp [hx.2]
  letI := Matrix.invertibleOfIsUnitDet x hd
  have h1 : x⁻¹.IsUpperTriangular := Matrix.blockTriangular_inv_of_blockTriangular hx.1
  unfold IsUpUni
  refine ⟨h1, fun a => ?_⟩
  have h := congrFun (congrFun (mul_inv_one_up hx) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, hx.2 a, one_mul, Matrix.one_apply_eq] at h
  · exact h
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h' | h'
    · rw [up_zero hx h', zero_mul]
    · have hz : x⁻¹ b a = 0 := h1 (show id a < id b from h')
      rw [hz, mul_zero]
  · simp
private lemma sum_superdiagonal_eq_sum_ite {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (∑ j : Fin n, if h : (j : ℕ) + 1 < n then M j ⟨j + 1, h⟩ else 0) =
      ∑ a : Fin n, ∑ c : Fin n, if (c : ℕ) = a + 1 then M a c else 0 := by
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨a + 1, h⟩ : Fin n)]
    · simp
    · intro b _ hb
      rw [if_neg (show ¬ ((b : ℕ) = a + 1) from fun e => hb (Fin.ext e))]
    · simp
  · symm
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg (show ¬ ((c : ℕ) = a + 1) from fun e => h (by have := c.2; omega))]
private lemma sum_subdiagonal_eq_sum_ite {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (∑ j : Fin n, if h : (j : ℕ) + 1 < n then M ⟨j + 1, h⟩ j else 0) =
      ∑ a : Fin n, ∑ c : Fin n, if (a : ℕ) = c + 1 then M a c else 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨c + 1, h⟩ : Fin n)]
    · simp
    · intro b _ hb
      rw [if_neg (show ¬ ((b : ℕ) = c + 1) from fun e => hb (Fin.ext e))]
    · simp
  · symm
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg (show ¬ ((a : ℕ) = c + 1) from fun e => h (by have := a.2; omega))]
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
theorem _root_.solution : PhaseWellDef := by
  unfold PhaseWellDef
  intro K _ s t x y hx hy h
  unfold sLow sUp
  have hyinv : y⁻¹ = ptI s t * x * pt s t := by
    apply Matrix.inv_eq_left_inv
    rw [show ptI s t * x * pt s t * y = ptI s t * (x * pt s t * y) by
      simp only [Matrix.mul_assoc], h, ptI_mul_pt]
  have hzU : IsUpUni y⁻¹ := isUpUni_inv_lower_unipotent_orbits hy
  have hz : ∀ a c, y⁻¹ (revF s a) (revF s c) =
      ↑(t (blk s a))⁻¹ * x a c * ↑(t (blk s c)) := by
    intro a c
    rw [hyinv, conj_apply]
    simp only [revF_revF, blk_revF]
  have hxz : ∀ a c : Fin s.sum, (a : ℕ) = c + 1 → blk s a ≠ blk s c → x a c = 0 := by
    intro a c hac hb
    have hlt : blk s c < blk s a :=
      lt_of_le_of_ne (blk_mono s c a (by omega)) (Ne.symm hb)
    have h0 := hz a c
    rw [up_zero hzU (revF_lt_of_blk_lt s hlt)] at h0
    exact (Units.mul_right_eq_zero _).1 ((Units.mul_left_eq_zero _).1 h0.symm)
  have hterm : ∀ a c : Fin s.sum,
      (if (revF s c : ℕ) = revF s a + 1 then ↑(t (blk s a))⁻¹ * x a c * ↑(t (blk s c)) else 0) =
      (if (a : ℕ) = c + 1 then x a c else 0) := by
    intro a c
    by_cases h1 : (a : ℕ) = c + 1
    · rw [if_pos h1]
      by_cases hb : blk s a = blk s c
      · have hs := revIn_succ s c (by have := a.2; omega) (by rw [← h1]; exact hb.symm)
        rw [← h1] at hs
        rw [if_pos (show (revF s c : ℕ) = revF s a + 1 by rw [revF_val, revF_val]; omega), hb,
          mul_assoc, mul_comm (x a c), ← mul_assoc, Units.inv_mul, one_mul]
      · rw [hxz a c h1 hb]
        simp
    · rw [if_neg h1]
      by_cases h2 : (revF s c : ℕ) = revF s a + 1
      · rw [if_pos h2]
        by_cases hb : blk s a = blk s c
        · exfalso
          have hs := revIn_succ s (revF s a) (by have := (revF s c).2; omega)
            (by rw [← h2, blk_revF, blk_revF, hb])
          rw [← h2] at hs
          have e1 : revIn s (revF s c) = c := congrArg Fin.val (revF_revF s c)
          have e2 : revIn s (revF s a) = a := congrArg Fin.val (revF_revF s a)
          omega
        · have hle : blk s a ≤ blk s c := by
            have := blk_mono s (revF s a) (revF s c) (by omega)
            rwa [blk_revF, blk_revF] at this
          have hlt : blk s a < blk s c := lt_of_le_of_ne hle hb
          have hac : a < c := by
            by_contra hca
            have := blk_mono s c a (not_lt.1 hca)
            omega
          rw [low_zero hx hac, mul_zero, zero_mul]
      · rw [if_neg h2]
  have hy1 := mul_inv_one_up hy
  have hyz : ∀ a c : Fin s.sum, (if (c : ℕ) = a + 1 then y a c else 0) =
      -(if (c : ℕ) = a + 1 then y⁻¹ a c else 0) := by
    intro a c
    split_ifs with hc
    · have := simple_add_zero hy hzU hy1 a c hc
      linear_combination this
    · simp
  rw [sum_subdiagonal_eq_sum_ite x, sum_superdiagonal_eq_sum_ite y]
  have hS : (∑ a : Fin s.sum, ∑ c : Fin s.sum, if (c : ℕ) = a + 1 then y a c else 0) =
      -∑ a : Fin s.sum, ∑ c : Fin s.sum, if (a : ℕ) = c + 1 then x a c else 0 := by
    calc (∑ a : Fin s.sum, ∑ c : Fin s.sum, if (c : ℕ) = a + 1 then y a c else 0)
        = -∑ a : Fin s.sum, ∑ c : Fin s.sum, if (c : ℕ) = a + 1 then y⁻¹ a c else 0 := by
          simp only [hyz, Finset.sum_neg_distrib]
      _ = -∑ a : Fin s.sum, ∑ c : Fin s.sum,
            if (revF s c : ℕ) = revF s a + 1 then y⁻¹ (revF s a) (revF s c) else 0 := by
          congr 1
          refine Fintype.sum_equiv (Function.Involutive.toPerm _ (revF_revF s)) _ _ fun a => ?_
          refine Fintype.sum_equiv (Function.Involutive.toPerm _ (revF_revF s)) _ _ fun c => ?_
          first
          | simp only [Function.Involutive.coe_toPerm, revF_revF]
          | simp [Function.Involutive.toPerm, revF_revF]
      _ = -∑ a : Fin s.sum, ∑ c : Fin s.sum, if (a : ℕ) = c + 1 then x a c else 0 := by
          congr 1
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
          rw [hz a c, hterm a c]
  rw [hS]
  ring
end Formalism.DoubleCosetMeasures.P.Phase
