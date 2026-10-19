-- Prove2me | solution 1 for BookProof.SmCar.car_creat_creat
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:58:50.432653+00:00
-- url     : https://prove2.me/submissions/1e695587-8ab9-4e98-8bb2-0ae5ecaa27df

import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
-- Generated from ChapterSmCarAlgebra.lean — theorem BookProof.SmCar.car_creat_creat
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.SmCar



open Finset

variable {n : ℕ}
theorem h42_annih_apply {n : ℕ} (i : Fin n) (ψ : BookProof.SmCar.FermiFock n) (S : Finset (Fin n)) :
    (BookProof.SmCar.annih i ψ) S = if i ∈ S then 0 else BookProof.SmCar.jwSign i S * ψ (insert i S) := rfl

theorem h42_creat_apply {n : ℕ} (i : Fin n) (ψ : BookProof.SmCar.FermiFock n) (S : Finset (Fin n)) :
    (BookProof.SmCar.creat i ψ) S = if i ∈ S then BookProof.SmCar.jwSign i (S.erase i) * ψ (S.erase i) else 0 := rfl

theorem h42_jw_insert {n : ℕ} {i j : Fin n} {S : Finset (Fin n)} (hj : j ∉ S) :
    BookProof.SmCar.jwSign i (insert j S) = (if j < i then -1 else 1) * BookProof.SmCar.jwSign i S := by
  unfold BookProof.SmCar.jwSign
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hj]), pow_succ]; ring
  · ring

theorem h42_jw_sq {n : ℕ} (i : Fin n) (S : Finset (Fin n)) : BookProof.SmCar.jwSign i S * BookProof.SmCar.jwSign i S = 1 := by
  unfold BookProof.SmCar.jwSign; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem h42_sign_prod {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    ((if j < i then (-1 : ℂ) else 1) * (if i < j then -1 else 1)) = -1 := by
  rcases lt_trichotomy i j with hl | hl | hl
  · simp [hl, not_lt.mpr hl.le]
  · exact absurd hl h
  · simp [hl, not_lt.mpr hl.le]

theorem h42_sign_sum {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    ((if j < i then (-1 : ℂ) else 1) + (if i < j then -1 else 1)) = 0 := by
  rcases lt_trichotomy i j with hl | hl | hl
  · simp [hl, not_lt.mpr hl.le]
  · exact absurd hl h
  · simp [hl, not_lt.mpr hl.le]

theorem h42_car_self {n : ℕ} (i : Fin n) :
    BookProof.SmCar.annih i ∘ₗ BookProof.SmCar.creat i + BookProof.SmCar.creat i ∘ₗ BookProof.SmCar.annih i = LinearMap.id := by
  ext1 ψ; ext S
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, PiLp.add_apply,
    h42_annih_apply, h42_creat_apply]
  by_cases h : i ∈ S
  · simp [h, Finset.insert_erase h, ← mul_assoc, h42_jw_sq]
  · simp [h, Finset.erase_insert h, ← mul_assoc, h42_jw_sq]

theorem h42_car_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    BookProof.SmCar.annih i ∘ₗ BookProof.SmCar.creat j + BookProof.SmCar.creat j ∘ₗ BookProof.SmCar.annih i = 0 := by
  ext1 ψ; ext S
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply, PiLp.add_apply,
    h42_annih_apply, h42_creat_apply, PiLp.zero_apply]
  by_cases hi : i ∈ S
  · simp [hi, Finset.mem_erase, hij]
  by_cases hj : j ∈ S
  · obtain ⟨T, hjT, rfl⟩ : ∃ T, j ∉ T ∧ S = insert j T := ⟨S.erase j, by simp, (insert_erase hj).symm⟩
    have hiT : i ∉ T := fun h => hi (mem_insert_of_mem h)
    have e1 : (insert i (insert j T)).erase j = insert i T := by
      rw [erase_insert_of_ne hij, erase_insert hjT]
    have hjiT : j ∉ insert i T := by simp [hjT, Ne.symm hij]
    have hm : j ∈ insert i (insert j T) := mem_insert_of_mem (mem_insert_self _ _)
    simp only [hi, if_false, mem_insert_self, if_true, e1, erase_insert hjT, hiT, hm]
    rw [h42_jw_insert hjT, h42_jw_insert hiT]
    have := h42_sign_prod hij
    linear_combination (BookProof.SmCar.jwSign i T * BookProof.SmCar.jwSign j T * ψ (insert i T)) * this
  · have : j ∉ insert i S := by simp [hj, Ne.symm hij]
    simp [hi, hj, this]

theorem h42_car_aa {n : ℕ} (i j : Fin n) :
    BookProof.SmCar.annih i ∘ₗ BookProof.SmCar.annih j + BookProof.SmCar.annih j ∘ₗ BookProof.SmCar.annih i = 0 := by
  ext1 ψ; ext S
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply, PiLp.add_apply,
    h42_annih_apply, PiLp.zero_apply]
  by_cases hij : i = j
  · subst hij; by_cases hi : i ∈ S <;> simp [hi]
  by_cases hi : i ∈ S
  · simp [hi]
  by_cases hj : j ∈ S
  · simp [hj]
  have h1 : j ∉ insert i S := by simp [hj, Ne.symm hij]
  have h2 : i ∉ insert j S := by simp [hi, hij]
  simp only [hi, hj, h1, h2, if_false]
  rw [h42_jw_insert hi, h42_jw_insert hj, Finset.insert_comm]
  have := h42_sign_sum hij
  linear_combination (BookProof.SmCar.jwSign i S * BookProof.SmCar.jwSign j S * ψ (insert i (insert j S))) * this

theorem h42_car_cc {n : ℕ} (i j : Fin n) :
    BookProof.SmCar.creat i ∘ₗ BookProof.SmCar.creat j + BookProof.SmCar.creat j ∘ₗ BookProof.SmCar.creat i = 0 := by
  ext1 ψ; ext S
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply, PiLp.add_apply,
    h42_creat_apply, PiLp.zero_apply]
  by_cases hij : i = j
  · subst hij; by_cases hi : i ∈ S <;> simp [hi]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨T, hjT, hiT, rfl⟩ : ∃ T, j ∉ T ∧ i ∉ T ∧ S = insert i (insert j T) :=
        ⟨(S.erase i).erase j, by simp, by simp, by
          rw [insert_erase (mem_erase.mpr ⟨Ne.symm hij, hj⟩), insert_erase hi]⟩
      have hjT' : j ∉ insert i T := by simp [hjT, Ne.symm hij]
      have hiT' : i ∉ insert j T := by simp [hiT, hij]
      have e1 : (insert i (insert j T)).erase i = insert j T := erase_insert hiT'
      have e2 : (insert i (insert j T)).erase j = insert i T := by
        rw [insert_comm]; exact erase_insert hjT'
      simp only [mem_insert_self, mem_insert_of_mem, if_true, e1, e2, erase_insert hjT,
        erase_insert hiT]
      rw [h42_jw_insert hjT, h42_jw_insert hiT]
      have := h42_sign_sum hij
      linear_combination (BookProof.SmCar.jwSign i T * BookProof.SmCar.jwSign j T * ψ T) * this
    · have : j ∉ S.erase i := fun h => hj (mem_of_mem_erase h)
      simp [hi, hj, this]
  · have : i ∉ S.erase j := fun h => hi (mem_of_mem_erase h)
    simp [hi, this]

theorem h42_flip_apply {n : ℕ} (i : Fin n) (S : Finset (Fin n)) :
    BookProof.SmCar.flipOcc i S = if i ∈ S then S.erase i else insert i S := rfl

theorem h42_jw_conj {n : ℕ} (i : Fin n) (S : Finset (Fin n)) : (starRingEnd ℂ) (BookProof.SmCar.jwSign i S) = BookProof.SmCar.jwSign i S := by
  simp [BookProof.SmCar.jwSign]

theorem h42_jw_norm {n : ℕ} (i : Fin n) (S : Finset (Fin n)) : ‖BookProof.SmCar.jwSign i S‖ = 1 := by
  simp [BookProof.SmCar.jwSign]

theorem h42_inner_eq {n : ℕ} (x y : BookProof.SmCar.FermiFock n) :
    (inner ℂ x y : ℂ) = ∑ S : Finset (Fin n), (starRingEnd ℂ) (x S) * y S := by
  simp [PiLp.inner_apply, mul_comm]

theorem h42_inner_annih {n : ℕ} (i : Fin n) (ψ φ : BookProof.SmCar.FermiFock n) :
    (inner ℂ (BookProof.SmCar.annih i ψ) φ : ℂ) = inner ℂ ψ (BookProof.SmCar.creat i φ) := by
  rw [h42_inner_eq, h42_inner_eq, ← (BookProof.SmCar.flipOcc i).sum_comp]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [h42_flip_apply, h42_creat_apply]
  by_cases h : i ∈ S
  · simp [h, h42_annih_apply, Finset.insert_erase h, h42_jw_conj]; ring
  · simp [h, h42_annih_apply]

theorem h42_inner_creat {n : ℕ} (i : Fin n) (ψ φ : BookProof.SmCar.FermiFock n) :
    (inner ℂ (BookProof.SmCar.creat i ψ) φ : ℂ) = inner ℂ ψ (BookProof.SmCar.annih i φ) := by
  rw [← inner_conj_symm, ← h42_inner_annih, inner_conj_symm]

theorem h42_norm_annih {n : ℕ} (i : Fin n) (ψ : BookProof.SmCar.FermiFock n) : ‖BookProof.SmCar.annih i ψ‖ ≤ ‖ψ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← (BookProof.SmCar.flipOcc i).sum_comp]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun S _ => ?_
  rw [h42_flip_apply, h42_annih_apply]
  by_cases h : i ∈ S
  · simp [h, Finset.insert_erase h, h42_jw_norm]
  · simp [h]

theorem h42_norm_creat {n : ℕ} (i : Fin n) (ψ : BookProof.SmCar.FermiFock n) : ‖BookProof.SmCar.creat i ψ‖ ≤ ‖ψ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← (BookProof.SmCar.flipOcc i).sum_comp]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun S _ => ?_
  rw [h42_flip_apply, h42_creat_apply]
  by_cases h : i ∈ S
  · simp [h]
  · simp [h, Finset.erase_insert h, h42_jw_norm]

theorem h42_fermiBilin_apply {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (ψ : BookProof.SmCar.FermiFock n) :
    BookProof.SmCar.fermiBilin h ψ = ∑ i : Fin n, ∑ j : Fin n, h i j • BookProof.SmCar.creat i (BookProof.SmCar.annih j ψ) := by
  simp [BookProof.SmCar.fermiBilin, LinearMap.sum_apply]

theorem h42_norm_bilin {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (ψ : BookProof.SmCar.FermiFock n) :
    ‖BookProof.SmCar.fermiBilin h ψ‖ ≤ (∑ i : Fin n, ∑ j : Fin n, ‖h i j‖) * ‖ψ‖ := by
  rw [h42_fermiBilin_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left ((h42_norm_creat _ _).trans (h42_norm_annih _ _)) (norm_nonneg _)

theorem h42_bilin_symm {n : ℕ} {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.conjTranspose = h)
    (ψ φ : BookProof.SmCar.FermiFock n) :
    (inner ℂ (BookProof.SmCar.fermiBilin h ψ) φ : ℂ) = inner ℂ ψ (BookProof.SmCar.fermiBilin h φ) := by
  rw [h42_fermiBilin_apply, h42_fermiBilin_apply]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, h42_inner_creat,
    h42_inner_annih]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : (starRingEnd ℂ) (h j i) = h i j := by
    have := congrFun (congrFun hh i) j
    simpa [Matrix.conjTranspose_apply] using this
  rw [this]

theorem solution (i j : Fin n) :
    BookProof.SmCar.creat i ∘ₗ BookProof.SmCar.creat j + BookProof.SmCar.creat j ∘ₗ BookProof.SmCar.creat i = 0 := by
  exact h42_car_cc i j

