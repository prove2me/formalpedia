-- Prove2me | solution 1 for BaconThesis.Collective.eq_8_32
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:45:50.411077+00:00
-- url     : https://prove2.me/submissions/53e45753-a0d5-4961-ab8d-be9f207df624

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_BaconThesis_Collective_onQubit
import Definitions.Def_BaconThesis_Collective_collS
import Definitions.Def_BaconThesis_Collective_levi

open scoped Matrix

namespace Aux_Bacon_832
open BaconThesis.Collective BBPSSW.Distill
open scoped Matrix

theorem mul_left_apply {n : ℕ} (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (x y : Fin n → Fin 2) :
    (onQubit i A * M) x y = ∑ c : Fin 2, A (x i) c * M (Function.update x i c) y := by
  rw [Matrix.mul_apply]
  have hinj : Function.Injective (fun c : Fin 2 => Function.update x i c) := by
    intro c c' h
    have := congrFun h i
    simpa using this
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image fun c => Function.update x i c)),
    Finset.sum_image (fun c _ c' _ h => hinj h)]
  · apply Finset.sum_congr rfl
    intro c _
    unfold onQubit
    rw [if_pos (fun k hk => by rw [Function.update_of_ne hk])]
    simp
  · intro z _ hz
    unfold onQubit
    rw [if_neg, zero_mul]
    intro hagree
    apply hz
    rw [Finset.mem_image]
    refine ⟨z i, Finset.mem_univ _, ?_⟩
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne hk]; exact hagree k hk

theorem same {n : ℕ} (i : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i A * onQubit i B = onQubit i (A * B) := by
  ext x y
  rw [mul_left_apply]
  by_cases h : ∀ k, k ≠ i → x k = y k
  · have h' : ∀ c : Fin 2, onQubit i B (Function.update x i c) y = B c (y i) := by
      intro c
      unfold onQubit
      rw [if_pos (fun k hk => by rw [Function.update_of_ne hk]; exact h k hk), Function.update_self]
    simp only [h']
    unfold onQubit
    rw [if_pos h, Matrix.mul_apply]
  · have h' : ∀ c : Fin 2, onQubit i B (Function.update x i c) y = 0 := by
      intro c
      unfold onQubit
      rw [if_neg]
      intro hc; apply h; intro k hk; rw [← hc k hk, Function.update_of_ne hk]
    simp only [h', mul_zero, Finset.sum_const_zero]
    unfold onQubit
    rw [if_neg h]

theorem cross_eq {n : ℕ} (i j : Fin n) (hij : i ≠ j) (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (x y : Fin n → Fin 2) :
    (onQubit i A * onQubit j B) x y =
      if (∀ k, k ≠ i → k ≠ j → x k = y k) then A (x i) (y i) * B (x j) (y j) else 0 := by
  rw [mul_left_apply]
  have hcond : ∀ c : Fin 2, (∀ k, k ≠ j → Function.update x i c k = y k) ↔
      (c = y i ∧ ∀ k, k ≠ i → k ≠ j → x k = y k) := by
    intro c
    constructor
    · intro h
      refine ⟨by simpa using h i hij, fun k hki hkj => ?_⟩
      rw [← h k hkj, Function.update_of_ne hki]
    · rintro ⟨rfl, h⟩ k hkj
      by_cases hki : k = i
      · subst hki; simp
      · rw [Function.update_of_ne hki]; exact h k hki hkj
  have hj : ∀ c : Fin 2, Function.update x i c j = x j := fun c =>
    Function.update_of_ne (Ne.symm hij) _ _
  simp only [onQubit, hj]
  by_cases hP : ∀ k, k ≠ i → k ≠ j → x k = y k
  · rw [if_pos hP]
    have : ∀ c : Fin 2, (if ∀ k, k ≠ j → Function.update x i c k = y k then B (x j) (y j) else 0)
        = if c = y i then B (x j) (y j) else 0 := by
      intro c
      by_cases hc : c = y i
      · rw [if_pos ((hcond c).mpr ⟨hc, hP⟩), if_pos hc]
      · rw [if_neg (fun h => hc ((hcond c).mp h).1), if_neg hc]
    simp only [this, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [if_neg hP]
    have : ∀ c : Fin 2, (if ∀ k, k ≠ j → Function.update x i c k = y k then B (x j) (y j) else 0)
        = 0 := by
      intro c
      rw [if_neg (fun h => hP ((hcond c).mp h).2)]
    simp only [this, mul_zero, Finset.sum_const_zero]

theorem cross {n : ℕ} (i j : Fin n) (hij : i ≠ j) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i A * onQubit j B = onQubit j B * onQubit i A := by
  ext x y
  rw [cross_eq i j hij, cross_eq j i (Ne.symm hij)]
  have : (∀ k, k ≠ i → k ≠ j → x k = y k) ↔ (∀ k, k ≠ j → k ≠ i → x k = y k) :=
    ⟨fun h k a b => h k b a, fun h k a b => h k b a⟩
  simp only [this]
  split_ifs <;> ring

theorem onQ_sub {n : ℕ} (i : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i A - onQubit i B = onQubit i (A - B) := by
  ext x y; simp only [onQubit, Matrix.sub_apply]; split_ifs <;> simp

theorem onQ_sum {n : ℕ} (i : Fin n) (f : Axis → ℂ) :
    onQubit i (∑ γ, f γ • pauli γ) = ∑ γ, f γ • onQubit i (pauli γ) := by
  ext x y
  simp only [onQubit, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem sum_axis (f : Axis → Matrix (Fin 2) (Fin 2) ℂ) : ∑ γ, f γ = f .x + f .y + f .z := by
  rw [show (Finset.univ : Finset Axis) = {.x, .y, .z} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

theorem pauli_comm (α β : Axis) :
    pauli α * pauli β - pauli β * pauli α =
      ∑ γ, (2 * Complex.I * (levi α β γ : ℂ)) • pauli γ := by
  rw [sum_axis]
  cases α <;> cases β <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, levi, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

end Aux_Bacon_832

open BaconThesis.Collective BBPSSW.Distill Aux_Bacon_832 in
theorem solution (n : ℕ) (α β : BBPSSW.Distill.Axis) :
    collS n α * collS n β - collS n β * collS n α =
      ∑ γ : BBPSSW.Distill.Axis, (Complex.I * (levi α β γ : ℂ)) • collS n γ := by
  unfold collS
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  have hoff : ∀ i : Fin n,
      (∑ j, ((1 / 2 : ℂ) • onQubit i (pauli α)) * ((1 / 2 : ℂ) • onQubit j (pauli β))) -
      (∑ j, ((1 / 2 : ℂ) • onQubit j (pauli β)) * ((1 / 2 : ℂ) • onQubit i (pauli α))) =
      (1 / 4 : ℂ) • onQubit i (pauli α * pauli β - pauli β * pauli α) := by
    intro i
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, same, same, onQ_sub]
      norm_num
    · intro j _ hj
      rw [smul_mul_smul_comm, smul_mul_smul_comm, cross i j (Ne.symm hj), sub_self]
    · simp
  rw [Finset.sum_congr rfl (fun i _ => hoff i)]
  simp only [pauli_comm, onQ_sum, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring
