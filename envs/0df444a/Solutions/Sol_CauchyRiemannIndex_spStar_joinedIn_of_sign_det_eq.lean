-- Prove2me | solution 1 for CauchyRiemannIndex.spStar_joinedIn_of_sign_det_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T15:46:41.105321+00:00
-- url     : https://prove2.me/submissions/a005a132-7a60-4c01-9ab9-b41df9d6e091

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_ConleyZehnder_spStar_exists_path_to_W
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Real.Sign

open Matrix CauchyRiemannIndex

namespace CRB1P

variable {n : ℕ}

lemma sign_eq_of_path (χ : C(unitInterval, Mat n)) (hχ : ∀ t, (1 - χ t).det ≠ 0) :
    Real.sign (1 - χ 1).det = Real.sign (1 - χ 0).det := by
  set f : unitInterval → ℝ := fun t => (1 - χ t).det with hf
  have hfc : Continuous f := by
    have : Continuous fun t => (1 : Mat n) - χ t := continuous_const.sub χ.continuous
    exact this.matrix_det
  have h0 : f 0 ≠ 0 := hχ 0
  have h1 : f 1 ≠ 0 := hχ 1
  have hnz : ∀ t, f t ≠ 0 := hχ
  have ivt := intermediate_value_univ (0 : unitInterval) 1 hfc
  have ivt' := intermediate_value_univ (1 : unitInterval) 0 hfc
  show Real.sign (f 1) = Real.sign (f 0)
  rcases h0.lt_or_gt with a | a <;> rcases h1.lt_or_gt with b | b
  · rw [Real.sign_of_neg a, Real.sign_of_neg b]
  · exfalso
    obtain ⟨t, ht⟩ := ivt ⟨a.le, b.le⟩
    exact hnz t ht
  · exfalso
    obtain ⟨t, ht⟩ := ivt' ⟨b.le, a.le⟩
    exact hnz t ht
  · rw [Real.sign_of_pos a, Real.sign_of_pos b]

lemma det_one_sub_Wplus : 0 < (1 - Wplus n).det := by
  unfold Wplus
  rw [sub_neg_eq_add, show (1 : Mat n) + 1 = (2 : ℝ) • (1 : Mat n) by rw [two_smul],
    det_smul, det_one, mul_one]
  positivity

lemma det_one_sub_Wminus (m : ℕ) : (1 - Wminus (m + 1)).det < 0 := by
  unfold Wminus
  rw [show (1 : Mat (m + 1)) = diagonal (fun _ => 1) from rfl, diagonal_sub, det_diagonal,
    Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.val_zero, if_true,
    Fin.val_succ, Nat.succ_ne_zero, if_false]
  norm_num

end CRB1P

open CRB1P in
theorem solution (n : ℕ) (A B : Mat n) (hA : A ∈ SpStar n)
    (hB : B ∈ SpStar n) (h : Real.sign (1 - A).det = Real.sign (1 - B).det) :
    JoinedIn (SpStar n) A B := by
  have key : ∀ C ∈ SpStar n, ∃ W, (W = Wplus n ∨ W = Wminus n) ∧ JoinedIn (SpStar n) C W ∧
      Real.sign (1 - W).det = Real.sign (1 - C).det := by
    intro C hC
    obtain ⟨χ, h0, hmem, h1⟩ := ConleyZehnder.spStar_exists_path_to_W C hC
    refine ⟨χ 1, h1, ⟨{ toContinuousMap := χ, source' := h0, target' := rfl }, hmem⟩, ?_⟩
    rw [← h0]; exact sign_eq_of_path χ fun t => (hmem t).2
  obtain ⟨WA, hWA, jA, sA⟩ := key A hA
  obtain ⟨WB, hWB, jB, sB⟩ := key B hB
  have hW : WA = WB := by
    rcases n with _ | m
    · exact Subsingleton.elim _ _
    · have hp : Real.sign (1 - Wplus (m + 1)).det = 1 := Real.sign_of_pos det_one_sub_Wplus
      have hm : Real.sign (1 - Wminus (m + 1)).det = -1 :=
        Real.sign_of_neg (det_one_sub_Wminus m)
      have hs : Real.sign (1 - WA).det = Real.sign (1 - WB).det := by rw [sA, sB, h]
      rcases hWA with rfl | rfl <;> rcases hWB with rfl | rfl
      · rfl
      · rw [hp, hm] at hs; norm_num at hs
      · rw [hp, hm] at hs; norm_num at hs
      · rfl
  rw [hW] at jA
  exact jA.trans jB.symm
