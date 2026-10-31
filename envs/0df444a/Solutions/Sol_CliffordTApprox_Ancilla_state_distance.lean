-- Prove2me | solution 1 for CliffordTApprox.Ancilla.state_distance
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:51:38.86449+00:00
-- url     : https://prove2.me/submissions/3317fa6a-ef9e-4f77-9434-175a2e0c9eff

import Definitions.Def_CliffordTApprox_Ancilla_Setting
import Theorems.Thm_CliffordTApprox_Ancilla_rounding_error
import Theorems.Thm_CliffordTApprox_Ancilla_norm_deficit

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P12
open CliffordTApprox.Ancilla

namespace CliffordTApprox.Ancilla

def qubits1Equiv : Qubits 1 ≃ Bool where
  toFun x := x 0
  invFun b := fun _ => b
  left_inv x := by
    funext i
    have : i = 0 := Subsingleton.elim i 0
    subst this
    rfl
  right_inv b := rfl

def qubits2Equiv : Qubits 2 ≃ Bool × Bool where
  toFun z := (z 0, z 1)
  invFun p i := if i = 0 then p.1 else p.2
  left_inv z := by
    funext i
    fin_cases i <;> rfl
  right_inv := by
    rintro ⟨a, b⟩
    have : (1 : Fin 2) ≠ 0 := by decide
    simp [this]

lemma qubits2_eq_zero :
    qubits2Equiv.symm (false, false) = (fun _ => false) := by
  funext i
  fin_cases i <;> rfl

lemma qubits2_ft_ne_zero :
    qubits2Equiv.symm (false, true) ≠ (fun _ => false) := by
  intro h
  have := congr_fun h 1
  revert this
  decide

lemma qubits2_tf_ne_zero :
    qubits2Equiv.symm (true, false) ≠ (fun _ => false) := by
  intro h
  have := congr_fun h 0
  revert this
  decide

lemma qubits2_tt_ne_zero :
    qubits2Equiv.symm (true, true) ≠ (fun _ => false) := by
  intro h
  have := congr_fun h 0
  revert this
  decide

lemma sum_qubits1 {α : Type*} [AddCommMonoid α] (f : Qubits 1 → α) :
    ∑ x : Qubits 1, f x = f (qubits1Equiv.symm true) + f (qubits1Equiv.symm false) := by
  have h := (Fintype.sum_equiv qubits1Equiv.symm (fun b => f (qubits1Equiv.symm b)) f (by intro; rfl)).symm
  rw [h, Fintype.sum_bool]

lemma sum_qubits2 {α : Type*} [AddCommMonoid α] (f : Qubits 2 → α) :
    ∑ z : Qubits 2, f z =
      f (qubits2Equiv.symm (true, true)) + f (qubits2Equiv.symm (true, false)) +
      (f (qubits2Equiv.symm (false, true)) + f (qubits2Equiv.symm (false, false))) := by
  have h := (Fintype.sum_equiv qubits2Equiv.symm (fun p => f (qubits2Equiv.symm p)) f (by intro; rfl)).symm
  rw [h, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]

lemma sum_qubits3 {α : Type*} [AddCommMonoid α] (f : Qubits (1 + 2) → α) :
    ∑ y : Qubits (1 + 2), f y =
      ∑ y1 : Qubits 1, ∑ y2 : Qubits 2, f ((qubitsAppendEquiv 1 2).symm (y1, y2)) := by
  have h := (Fintype.sum_equiv (qubitsAppendEquiv 1 2).symm
    (fun p => f ((qubitsAppendEquiv 1 2).symm p)) f (by intro; rfl)).symm
  rw [h, Fintype.sum_prod_type]

lemma frobNorm_eq {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) :
    frobNorm X = Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) := by
  have h1 : frobNorm X = (∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    @Matrix.frobenius_norm_def m n ℂ _ _ _ X
  have h2 : (∑ i, ∑ j, ‖X i j‖ ^ (2 : ℝ)) = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
    simp_rw [Real.rpow_two]
  rw [h1, h2, ← Real.sqrt_eq_rpow]

lemma idealMap_apply (φ : ℝ) (y : Qubits (1 + 2)) (x : Qubits 1) :
    idealMap (phaseGate φ) 2 y x =
      if (qubitsAppendEquiv 1 2 y).2 = (fun _ => false) then
        if (qubitsAppendEquiv 1 2 y).1 0 = x 0 then
          if x 0 then Complex.exp (φ * Complex.I) else 1
        else 0
      else 0 := by
  dsimp [idealMap, phaseGate, oneQubit, Matrix.submatrix, Matrix.diagonal]
  by_cases h2 : (qubitsAppendEquiv 1 2 y).2 = (fun _ => false)
  · rw [if_pos h2, if_pos h2]
    by_cases h1 : (qubitsAppendEquiv 1 2 y).1 0 = x 0
    · rw [if_pos h1, if_pos h1, h1]
    · rw [if_neg h1, if_neg h1]
  · rw [if_neg h2, if_neg h2]

lemma act_ket {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (j y : ι) :
    (act A (ket j)) y = A y j := by
  dsimp [act, ket, Matrix.mulVec, EuclideanSpace.single]
  simp

lemma eq_append_iff (z : Qubits (1 + 2)) (x : Qubits 1) :
    z = Fin.append x (fun _ => false) ↔
    ((qubitsAppendEquiv 1 2) z).1 0 = x 0 ∧ ((qubitsAppendEquiv 1 2) z).2 = (fun _ => false) := by
  constructor
  · rintro rfl
    simp [qubitsAppendEquiv]
  · rintro ⟨h1, h2⟩
    have he : z = (qubitsAppendEquiv 1 2).symm ((qubitsAppendEquiv 1 2) z) := by simp
    rw [he]
    dsimp [qubitsAppendEquiv]
    congr
    funext i
    have : i = 0 := Subsingleton.elim i 0
    subst this
    exact h1

lemma dataTensor_ket_zero (x : Qubits 1) :
    dataTensor (x 0) (ket (fun _ : Fin 2 => false)) = ket (Fin.append x (fun _ : Fin 2 => false)) := by
  ext z
  dsimp [dataTensor, ket, EuclideanSpace.single]
  rw [Pi.single_apply, Pi.single_apply]
  by_cases hz : z = Fin.append x (fun _ => false)
  · rw [if_pos hz]
    rw [eq_append_iff] at hz
    rw [if_pos hz.1, if_pos hz.2]
  · rw [if_neg hz]
    by_cases h1 : ((qubitsAppendEquiv 1 2) z).1 0 = x 0
    · rw [if_pos h1]
      have h2 : ¬ ((qubitsAppendEquiv 1 2) z).2 = (fun _ => false) := by
        intro h2
        apply hz
        rw [eq_append_iff]
        exact ⟨h1, h2⟩
      rw [if_neg h2]
    · rw [if_neg h1]

lemma initializedMap_apply (W : Matrix (Qubits (1 + 2)) (Qubits (1 + 2)) ℂ)
    (v : EuclideanSpace ℂ (Qubits 2)) (hW : PreparesControlled W v)
    (y : Qubits (1 + 2)) (x : Qubits 1) :
    initializedMap W y x =
      if x 0 then (dataTensor true v) y
      else (dataTensor false (ket (fun _ => false))) y := by
  dsimp [initializedMap]
  have h_act := (act_ket W (Fin.append x (fun _ => false)) y).symm
  rw [h_act, ← dataTensor_ket_zero]
  by_cases hx : x 0 = true
  · rw [hx, if_pos rfl, hW.2]
  · have hx' : x 0 = false := Bool.eq_false_of_not_eq_true hx
    rw [hx', if_neg (by decide), hW.1]

lemma matrix_sub_apply_false (W : Matrix (Qubits (1 + 2)) (Qubits (1 + 2)) ℂ)
    (v : EuclideanSpace ℂ (Qubits 2)) (hW : PreparesControlled W v)
    (φ : ℝ) (y : Qubits (1 + 2)) (x : Qubits 1) (hx : x 0 = false) :
    (initializedMap W - idealMap (phaseGate φ) 2) y x = 0 := by
  dsimp
  rw [initializedMap_apply W v hW, idealMap_apply, hx]
  dsimp [dataTensor, ket, EuclideanSpace.single]
  rw [Pi.single_apply]
  split_ifs <;> ring

lemma matrix_sub_apply_true (W : Matrix (Qubits (1 + 2)) (Qubits (1 + 2)) ℂ)
    (v : EuclideanSpace ℂ (Qubits 2)) (hW : PreparesControlled W v)
    (φ : ℝ) (y : Qubits (1 + 2)) (x : Qubits 1) (hx : x 0 = true) :
    (initializedMap W - idealMap (phaseGate φ) 2) y x =
      if (qubitsAppendEquiv 1 2 y).1 0 then
        v (qubitsAppendEquiv 1 2 y).2 -
          (if (qubitsAppendEquiv 1 2 y).2 = (fun _ => false) then Complex.exp (φ * Complex.I) else 0)
      else 0 := by
  dsimp
  rw [initializedMap_apply W v hW, idealMap_apply, hx]
  dsimp [dataTensor]
  split_ifs <;> ring

lemma X_apply_true (W : Matrix (Qubits (1 + 2)) (Qubits (1 + 2)) ℂ)
    (v : EuclideanSpace ℂ (Qubits 2)) (hW : PreparesControlled W v)
    (φ : ℝ) (y1 : Qubits 1) (y2 : Qubits 2) :
    (initializedMap W - idealMap (phaseGate φ) 2) ((qubitsAppendEquiv 1 2).symm (y1, y2)) (qubits1Equiv.symm true) =
      if y1 0 then
        v y2 - (if y2 = (fun _ => false) then Complex.exp (φ * Complex.I) else 0)
      else 0 := by
  have h_proj : qubitsAppendEquiv 1 2 ((qubitsAppendEquiv 1 2).symm (y1, y2)) = (y1, y2) :=
    Equiv.apply_symm_apply (qubitsAppendEquiv 1 2) (y1, y2)
  have h_app := matrix_sub_apply_true W v hW φ ((qubitsAppendEquiv 1 2).symm (y1, y2)) (qubits1Equiv.symm true) rfl
  have h1 : (qubitsAppendEquiv 1 2 ((qubitsAppendEquiv 1 2).symm (y1, y2))).1 0 = y1 0 := by
    rw [h_proj]
  have h2 : (qubitsAppendEquiv 1 2 ((qubitsAppendEquiv 1 2).symm (y1, y2))).2 = y2 := by
    rw [h_proj]
  rw [h_app, h1, h2]

lemma complex_norm_sq_div (u v : ℤ) (k : ℕ) :
    ‖((u : ℂ) + (v : ℂ) * Complex.I) / (2 : ℂ) ^ k‖ ^ 2 = ((u : ℝ) ^ 2 + (v : ℝ) ^ 2) / (4 : ℝ) ^ k := by
  rw [← Complex.normSq_eq_norm_sq, map_div₀, map_pow]
  have h1 : Complex.normSq ((u : ℂ) + (v : ℂ) * Complex.I) = (u : ℝ) ^ 2 + (v : ℝ) ^ 2 := by
    have hu : (u : ℂ) = ((u : ℝ) : ℂ) := by push_cast; rfl
    have hv : (v : ℂ) = ((v : ℝ) : ℂ) := by push_cast; rfl
    rw [hu, hv, Complex.normSq_add_mul_I]
  have h2 : Complex.normSq (2 : ℂ) = 4 := by norm_num
  rw [h1, h2]

lemma rounding_sq_le (k : ℕ) (φ : ℝ) (hφ₀ : 0 ≤ φ) (hφ₁ : φ ≤ Real.pi / 4) :
    ‖gammaApprox k φ - Complex.exp (φ * Complex.I)‖ ^ 2 ≤ 2 / (4 : ℝ) ^ k := by
  have h := rounding_error k φ hφ₀ hφ₁
  have h0 : 0 ≤ ‖gammaApprox k φ - Complex.exp (φ * Complex.I)‖ := norm_nonneg _
  have h_sq : ‖gammaApprox k φ - Complex.exp (φ * Complex.I)‖ ^ 2 ≤ (Real.sqrt 2 / (2 : ℝ) ^ k) ^ 2 := by
    nlinarith
  have h_pow : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
    rw [sq, ← mul_pow]
    norm_num
  have h_val : (Real.sqrt 2 / (2 : ℝ) ^ k) ^ 2 = 2 / (4 : ℝ) ^ k := by
    rw [div_pow, Real.sq_sqrt (by norm_num), h_pow]
  rwa [h_val] at h_sq

end CliffordTApprox.Ancilla

theorem solution (k : ℕ) (φ : ℝ) (hφ₀ : 0 ≤ φ) (hφ₁ : φ ≤ Real.pi / 4)
    (a b c d : ℤ) (habcd : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = deficit k φ)
    (W : Matrix (Qubits (1 + 2)) (Qubits (1 + 2)) ℂ)
    (hW : PreparesControlled W (vecV k φ a b c d)) :
    frobNorm (initializedMap W - idealMap (phaseGate φ) 2) ≤
      Real.sqrt (2 / 4 ^ k + 2 * Real.sqrt 2 / 2 ^ k) := by
  let v := vecV k φ a b c d
  rw [frobNorm_eq]
  have h_sum_comm : ∑ i, ∑ j, ‖(initializedMap W - idealMap (phaseGate φ) 2) i j‖ ^ 2 =
      ∑ j, ∑ i, ‖(initializedMap W - idealMap (phaseGate φ) 2) i j‖ ^ 2 := Finset.sum_comm
  rw [h_sum_comm, sum_qubits1]
  have h_false_term : ∑ i : Qubits (1 + 2), ‖(initializedMap W - idealMap (phaseGate φ) 2) i (qubits1Equiv.symm false)‖ ^ 2 = 0 := by
    have h_entry : ∀ i, (initializedMap W - idealMap (phaseGate φ) 2) i (qubits1Equiv.symm false) = 0 := by
      intro i
      exact matrix_sub_apply_false W v hW φ i (qubits1Equiv.symm false) rfl
    simp [h_entry]
  rw [h_false_term, add_zero]
  -- Now evaluate the sum over Qubits (1 + 2) for x = qubits1Equiv.symm true
  rw [sum_qubits3]
  have h_y_sum : ∑ y1 : Qubits 1, ∑ y2 : Qubits 2, ‖(initializedMap W - idealMap (phaseGate φ) 2) ((qubitsAppendEquiv 1 2).symm (y1, y2)) (qubits1Equiv.symm true)‖ ^ 2 =
      ∑ y2 : Qubits 2, ‖(initializedMap W - idealMap (phaseGate φ) 2) ((qubitsAppendEquiv 1 2).symm (qubits1Equiv.symm true, y2)) (qubits1Equiv.symm true)‖ ^ 2 := by
    rw [sum_qubits1]
    have h_y_false : ∑ y2 : Qubits 2, ‖(initializedMap W - idealMap (phaseGate φ) 2) ((qubitsAppendEquiv 1 2).symm (qubits1Equiv.symm false, y2)) (qubits1Equiv.symm true)‖ ^ 2 = 0 := by
      have h_zero : ∀ y2, (initializedMap W - idealMap (phaseGate φ) 2) ((qubitsAppendEquiv 1 2).symm (qubits1Equiv.symm false, y2)) (qubits1Equiv.symm true) = 0 := by
        intro y2
        rw [X_apply_true W v hW φ (qubits1Equiv.symm false) y2]
        rfl
      simp [h_zero]
    rw [h_y_false, add_zero]
  rw [h_y_sum]
  have h_inner_sq : (∑ y2 : Qubits 2, ‖(initializedMap W - idealMap (phaseGate φ) 2) ((qubitsAppendEquiv 1 2).symm (qubits1Equiv.symm true, y2)) (qubits1Equiv.symm true)‖ ^ 2) =
      ∑ y2 : Qubits 2, ‖v y2 - (if y2 = (fun _ => false) then Complex.exp (φ * Complex.I) else 0)‖ ^ 2 := by
    congr 1
    funext y2
    rw [X_apply_true W v hW φ (qubits1Equiv.symm true) y2]
    rfl
  rw [h_inner_sq, sum_qubits2]
  -- Evaluate the 4 cases of y2
  have h_case_ff : ‖v (qubits2Equiv.symm (false, false)) - (if (qubits2Equiv.symm (false, false)) = (fun _ => false) then Complex.exp (φ * Complex.I) else 0)‖ ^ 2 =
      ‖gammaApprox k φ - Complex.exp (φ * Complex.I)‖ ^ 2 := by
    rw [qubits2_eq_zero, if_pos rfl]
    dsimp [v, vecV]
  have h_case_ft : ‖v (qubits2Equiv.symm (false, true)) - (if (qubits2Equiv.symm (false, true)) = (fun _ => false) then Complex.exp (φ * Complex.I) else 0)‖ ^ 2 = 0 := by
    rw [if_neg qubits2_ft_ne_zero, sub_zero]
    dsimp [v, vecV, qubits2Equiv]
    simp
  have h_case_tf : ‖v (qubits2Equiv.symm (true, false)) - (if (qubits2Equiv.symm (true, false)) = (fun _ => false) then Complex.exp (φ * Complex.I) else 0)‖ ^ 2 =
      ‖((a : ℂ) + (b : ℂ) * Complex.I) / (2 : ℂ) ^ k‖ ^ 2 := by
    rw [if_neg qubits2_tf_ne_zero, sub_zero]
    dsimp [v, vecV, qubits2Equiv]
  have h_case_tt : ‖v (qubits2Equiv.symm (true, true)) - (if (qubits2Equiv.symm (true, true)) = (fun _ => false) then Complex.exp (φ * Complex.I) else 0)‖ ^ 2 =
      ‖((c : ℂ) + (d : ℂ) * Complex.I) / (2 : ℂ) ^ k‖ ^ 2 := by
    rw [if_neg qubits2_tt_ne_zero, sub_zero]
    dsimp [v, vecV, qubits2Equiv]
  rw [h_case_tt, h_case_tf, h_case_ft, h_case_ff, zero_add]
  -- Now rewrite norm squares of (a+bI)/2^k and (c+dI)/2^k
  rw [complex_norm_sq_div a b k, complex_norm_sq_div c d k]
  have h_frac_add : ((c : ℝ) ^ 2 + (d : ℝ) ^ 2) / 4 ^ k + ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / 4 ^ k =
      ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℤ) : ℝ) / 4 ^ k := by
    rw [← add_div]
    push_cast
    ring
  rw [h_frac_add]
  have h_nd := norm_deficit k φ hφ₀ hφ₁
  have h_tail_eq := h_nd.2.2 a b c d habcd
  rw [h_tail_eq]
  have h_round := rounding_sq_le k φ hφ₀ hφ₁
  have h_sum_le : ((1 - ‖gammaApprox k φ‖ ^ 2) + ‖gammaApprox k φ - Complex.exp (φ * Complex.I)‖ ^ 2) ≤
      2 / (4 : ℝ) ^ k + 2 * Real.sqrt 2 / (2 : ℝ) ^ k := by
    linarith [h_nd.2.1]
  apply Real.sqrt_le_sqrt h_sum_le
