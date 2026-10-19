-- Prove2me | solution 1 for BookProof.SmDiracYukawa.diagOp_normSq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:20:17.114913+00:00
-- url     : https://prove2.me/submissions/5ab6bd5e-b83e-4c22-8894-1d4030ce3c99

import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterSmCarAlgebra
-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.diagOp_normSq
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.SmCar
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section
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

theorem h42_diag_apply {n : ℕ} (d : Finset (Fin n) → ℝ) (ψ : FermiFock n) (S : Finset (Fin n)) :
    (diagOp d ψ) S = (d S : ℂ) * ψ S := rfl

theorem h42_diag_normSq {n : ℕ} (d : Finset (Fin n) → ℝ) (ψ : FermiFock n) :
    ‖diagOp d ψ‖ ^ 2 = ∑ S : Finset (Fin n), (d S) ^ 2 * ‖ψ S‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [h42_diag_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem h42_diag_inner {n : ℕ} (d : Finset (Fin n) → ℝ) (ψ : FermiFock n) :
    (inner ℂ ψ (diagOp d ψ) : ℂ)
      = ∑ S : Finset (Fin n), ((d S * ‖ψ S‖ ^ 2 : ℝ) : ℂ) := by
  simp only [PiLp.inner_apply, h42_diag_apply]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [RCLike.inner_apply, mul_assoc, Complex.mul_conj']
  push_cast; ring

theorem h42_diag_ge {n : ℕ} {d : Finset (Fin n) → ℝ} (hd : ∀ S, 1 ≤ d S) (ψ : FermiFock n) :
    ‖ψ‖ ≤ ‖diagOp d ψ‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), h42_diag_normSq, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_le_sum fun S _ => ?_
  have h1 : 1 ≤ d S ^ 2 := by nlinarith [hd S]
  nlinarith [sq_nonneg ‖ψ S‖]

theorem h42_diag_le {n : ℕ} {d : Finset (Fin n) → ℝ} {Om : ℝ} (hOm : 0 ≤ Om)
    (hd : ∀ S, |d S| ≤ Om) (ψ : FermiFock n) : ‖diagOp d ψ‖ ≤ Om * ‖ψ‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), h42_diag_normSq, mul_pow,
    EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun S _ => ?_
  have h1 : d S ^ 2 ≤ Om ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hd S) 2
  exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)

theorem h42_diag_surj {n : ℕ} {d : Finset (Fin n) → ℝ} (hd : ∀ S, 1 ≤ d S)
    (f : FermiFock n) : ∃ ψ : FermiFock n, diagOp d ψ + ψ = f := by
  refine ⟨WithLp.toLp 2 (fun S => f S / ((d S : ℂ) + 1)), ?_⟩
  ext S
  rw [PiLp.add_apply, h42_diag_apply]
  have : (d S : ℂ) + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [hd S]
  field_simp

theorem h42_creat_annih_apply {n : ℕ} (i : Fin n) (ψ : FermiFock n) (S : Finset (Fin n)) :
    (creat i (annih i ψ)) S = if i ∈ S then ψ S else 0 := by
  show (if i ∈ S then jwSign i (S.erase i) * (if i ∈ S.erase i then 0 else
    jwSign i (S.erase i) * ψ (insert i (S.erase i))) else 0) = _
  by_cases h : i ∈ S
  · have hs : jwSign i (S.erase i) * jwSign i (S.erase i) = 1 := by
      unfold jwSign; rw [← pow_add, ← two_mul, pow_mul]; simp
    simp [h, Finset.insert_erase h, ← mul_assoc, hs]
  · simp [h]

theorem h42_sum_apply {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → FermiFock n) (S : Finset (Fin n)) :
    (∑ i ∈ s, f i) S = ∑ i ∈ s, (f i) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

theorem h42_energy_apply {n : ℕ} (om : Fin n → ℝ) (ψ : FermiFock n) :
    fermiEnergy om ψ = ∑ i, (om i : ℂ) • creat i (annih i ψ) := by
  simp [fermiEnergy, fermiBilin, LinearMap.sum_apply, Matrix.diagonal_apply, ite_smul]

theorem h42_N_eq {n : ℕ} (om : Fin n → ℝ) (c0 : ℝ) :
    smFermiN om c0 = diagOp (smFermiWeight om c0) := by
  ext1 ψ; ext S
  simp only [smFermiN, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    PiLp.add_apply, PiLp.smul_apply, h42_diag_apply, smFermiWeight, h42_energy_apply,
    h42_sum_apply, smul_eq_mul, h42_creat_annih_apply]
  push_cast
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [add_mul, Finset.sum_mul]

theorem h42_weight_ge {n : ℕ} {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0)
    (S : Finset (Fin n)) : 1 ≤ smFermiWeight om c0 S := by
  unfold smFermiWeight
  have := Finset.sum_nonneg (s := S) (fun i _ => hom i)
  linarith

theorem h42_weight_le {n : ℕ} {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0)
    (S : Finset (Fin n)) : |smFermiWeight om c0 S| ≤ smFermiOm om c0 := by
  rw [abs_of_nonneg (by linarith [h42_weight_ge hom hc0 S])]
  unfold smFermiWeight smFermiOm
  have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => hom i)
  linarith

theorem h42_Om_ge {n : ℕ} {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) :
    1 ≤ smFermiOm om c0 := by
  have := h42_weight_ge hom hc0 ∅
  have h2 := h42_weight_le hom hc0 ∅
  linarith [le_abs_self (smFermiWeight om c0 ∅)]

theorem h42_N_ge {n : ℕ} {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0)
    (ψ : FermiFock n) : ‖ψ‖ ≤ ‖smFermiN om c0 ψ‖ := by
  rw [h42_N_eq]; exact h42_diag_ge (h42_weight_ge hom hc0) ψ

theorem h42_N_le {n : ℕ} {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0)
    (ψ : FermiFock n) : ‖smFermiN om c0 ψ‖ ≤ smFermiOm om c0 * ‖ψ‖ := by
  rw [h42_N_eq]
  exact h42_diag_le (by linarith [h42_Om_ge hom hc0]) (h42_weight_le hom hc0) ψ

theorem h42_N_surj {n : ℕ} {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0)
    (f : FermiFock n) :
    ∃ x : fullDom n, onFull (smFermiN om c0) x + (x : FermiFock n) = f := by
  obtain ⟨ψ, hψ⟩ := h42_diag_surj (h42_weight_ge hom hc0) f
  refine ⟨⟨ψ, Submodule.mem_top⟩, ?_⟩
  show smFermiN om c0 ψ + ψ = f
  rw [h42_N_eq]; exact hψ

theorem h42_quadN {n : ℕ} {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0)
    (ψ : FermiFock n) : ‖ψ‖ ^ 2 ≤ (inner ℂ ψ (smFermiN om c0 ψ) : ℂ).re := by
  rw [h42_N_eq, h42_diag_inner, Complex.re_sum, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_le_sum fun S _ => ?_
  rw [Complex.ofReal_re]
  have := h42_weight_ge hom hc0 S
  nlinarith [sq_nonneg ‖ψ S‖]

theorem h42_matrix_herm {n : ℕ} {hD M : Matrix (Fin n) (Fin n) ℂ} (z : ℂ)
    (hh : hD.conjTranspose = hD) : (smFermiMatrix hD M z).conjTranspose = smFermiMatrix hD M z := by
  simp only [smFermiMatrix, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, hh]
  abel

theorem h42_ham_symm {n : ℕ} {hD M : Matrix (Fin n) (Fin n) ℂ} (z : ℂ)
    (hh : hD.conjTranspose = hD) (ψ φ : FermiFock n) :
    (inner ℂ (smFermiHam hD M z ψ) φ : ℂ) = inner ℂ ψ (smFermiHam hD M z φ) :=
  h42_bilin_symm (h42_matrix_herm z hh) ψ φ

theorem h42_ham_le {n : ℕ} (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (ψ : FermiFock n) :
    ‖smFermiHam hD M z ψ‖ ≤ smFermiBound hD M z * ‖ψ‖ :=
  h42_norm_bilin _ ψ

theorem h42_bound_nonneg {n : ℕ} (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    0 ≤ smFermiBound hD M z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem h42_ham_symmOn {n : ℕ} {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ}
    (hh : hD.conjTranspose = hD) :
    SymmetricOn (fullDom n) (onFull (smFermiHam hD M z)) := by
  intro x y; exact h42_ham_symm z hh x y

theorem h42_esa {n : ℕ} {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ}
    (hh : hD.conjTranspose = hD) :
    EssentiallySelfAdjointOn (fullDom n)
      ((onFull (smFermiHam hD M z)).comp (Submodule.inclusion (le_refl (fullDom n)))) := by
  have key : ∀ c : ℂ, c.re = 0 → c ≠ 0 →
      DeficiencyTrivialAt (fullDom n)
        ((onFull (smFermiHam hD M z)).comp (Submodule.inclusion (le_refl (fullDom n)))) c := by
    intro c hc hc0 w hw
    have h1 := hw ⟨w, Submodule.mem_top⟩
    change (inner ℂ (smFermiHam hD M z w) w : ℂ) = c * inner ℂ w w at h1
    have hr : (inner ℂ (smFermiHam hD M z w) w : ℂ).im = 0 := by
      have hs := h42_ham_symm (M := M) z hh w w
      have hc2 := inner_conj_symm (𝕜 := ℂ) (smFermiHam hD M z w) w
      rw [hs] at hc2
      rw [hs]; exact Complex.conj_eq_iff_im.mp hc2
    rw [h1, inner_self_eq_norm_sq_to_K] at hr
    have hc' : c.im ≠ 0 := fun h => hc0 (Complex.ext hc h)
    have : c.im * ‖w‖ ^ 2 = 0 := by
      have e : (c * ((‖w‖ : ℂ) ^ 2)).im = c.im * ‖w‖ ^ 2 := by
        rw [← Complex.ofReal_pow, Complex.im_mul_ofReal]
      exact e ▸ hr
    have : ‖w‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hc'
      · exact h
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  exact ⟨key _ (by simp) Complex.I_ne_zero, key _ (by simp) (neg_ne_zero.mpr Complex.I_ne_zero)⟩

theorem h42_fl_i {n : ℕ} {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}
    (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (x : fullDom n) :
    |quadForm (onFull (smFermiHam hD M z)) x|
      ≤ smFermiBound hD M z * quadForm (onFull (smFermiN om c0)) x := by
  have hq := h42_quadN hom hc0 (x : FermiFock n)
  change |(inner ℂ (x : FermiFock n) (smFermiHam hD M z x) : ℂ).re|
    ≤ smFermiBound hD M z * (inner ℂ (x : FermiFock n) (smFermiN om c0 x) : ℂ).re
  calc _ ≤ ‖(inner ℂ (x : FermiFock n) (smFermiHam hD M z x) : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(x : FermiFock n)‖ * ‖smFermiHam hD M z x‖ := norm_inner_le_norm _ _
    _ ≤ ‖(x : FermiFock n)‖ * (smFermiBound hD M z * ‖(x : FermiFock n)‖) :=
        mul_le_mul_of_nonneg_left (h42_ham_le _ _ _ _) (norm_nonneg _)
    _ = smFermiBound hD M z * ‖(x : FermiFock n)‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hq (h42_bound_nonneg _ _ _)

theorem h42_fl_ii {n : ℕ} {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}
    (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (x : fullDom n) :
    |commForm (onFull (smFermiHam hD M z)) (onFull (smFermiN om c0)) x|
      ≤ (2 * smFermiBound hD M z * smFermiOm om c0)
        * quadForm (onFull (smFermiN om c0)) x := by
  have hq := h42_quadN hom hc0 (x : FermiFock n)
  change |(Complex.I * ((inner ℂ (smFermiHam hD M z (x : FermiFock n)) (smFermiN om c0 (x : FermiFock n)) : ℂ)
      - (inner ℂ (smFermiN om c0 (x : FermiFock n)) (smFermiHam hD M z (x : FermiFock n)) : ℂ))).re|
    ≤ (2 * smFermiBound hD M z * smFermiOm om c0) * (inner ℂ (x : FermiFock n) (smFermiN om c0 (x : FermiFock n)) : ℂ).re
  have hB := h42_bound_nonneg hD M z
  have hO := h42_Om_ge hom hc0
  have hH := h42_ham_le hD M z (x : FermiFock n)
  have hN := h42_N_le hom hc0 (x : FermiFock n)
  have hnH := norm_nonneg (smFermiHam hD M z (x : FermiFock n))
  have hnN := norm_nonneg (smFermiN om c0 (x : FermiFock n))
  have hnv := norm_nonneg (x : FermiFock n)
  calc _ ≤ ‖Complex.I * ((inner ℂ (smFermiHam hD M z (x : FermiFock n)) (smFermiN om c0 (x : FermiFock n)) : ℂ)
      - (inner ℂ (smFermiN om c0 (x : FermiFock n)) (smFermiHam hD M z (x : FermiFock n)) : ℂ))‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(inner ℂ (smFermiHam hD M z (x : FermiFock n)) (smFermiN om c0 (x : FermiFock n)) : ℂ)‖
        + ‖(inner ℂ (smFermiN om c0 (x : FermiFock n)) (smFermiHam hD M z (x : FermiFock n)) : ℂ)‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]; exact norm_sub_le _ _
    _ ≤ ‖smFermiHam hD M z (x : FermiFock n)‖ * ‖smFermiN om c0 (x : FermiFock n)‖ + ‖smFermiN om c0 (x : FermiFock n)‖ * ‖smFermiHam hD M z (x : FermiFock n)‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = 2 * (‖smFermiHam hD M z (x : FermiFock n)‖ * ‖smFermiN om c0 (x : FermiFock n)‖) := by ring
    _ ≤ 2 * ((smFermiBound hD M z * ‖(x : FermiFock n)‖) * (smFermiOm om c0 * ‖(x : FermiFock n)‖)) := by
        gcongr
    _ = (2 * smFermiBound hD M z * smFermiOm om c0) * ‖(x : FermiFock n)‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)

theorem h42_dcomm_le {n : ℕ} {H N : FermiFock n →ₗ[ℂ] FermiFock n} {K Om : ℝ}
    (hK : ∀ ψ, ‖H ψ‖ ≤ K * ‖ψ‖) (hN : ∀ ψ, ‖N ψ‖ ≤ Om * ‖ψ‖) (hKn : 0 ≤ K) (hOn : 0 ≤ Om)
    (ψ : FermiFock n) : ‖dcommOp H N ψ‖ ≤ 4 * K * Om ^ 2 * ‖ψ‖ := by
  have e : dcommOp H N ψ = N (N (H ψ)) - N (H (N ψ)) - (N (H (N ψ)) - H (N (N ψ))) := by
    simp only [dcommOp, Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, map_sub]
  rw [e]
  have h1 : ‖N (N (H ψ))‖ ≤ Om * (Om * (K * ‖ψ‖)) :=
    (hN _).trans (mul_le_mul_of_nonneg_left ((hN _).trans
      (mul_le_mul_of_nonneg_left (hK _) hOn)) hOn)
  have h2 : ‖N (H (N ψ))‖ ≤ Om * (K * (Om * ‖ψ‖)) :=
    (hN _).trans (mul_le_mul_of_nonneg_left ((hK _).trans
      (mul_le_mul_of_nonneg_left (hN _) hKn)) hOn)
  have h3 : ‖H (N (N ψ))‖ ≤ K * (Om * (Om * ‖ψ‖)) :=
    (hK _).trans (mul_le_mul_of_nonneg_left ((hN _).trans
      (mul_le_mul_of_nonneg_left (hN _) hOn)) hKn)
  calc _ ≤ ‖N (N (H ψ)) - N (H (N ψ))‖ + ‖N (H (N ψ)) - H (N (N ψ))‖ := norm_sub_le _ _
    _ ≤ (‖N (N (H ψ))‖ + ‖N (H (N ψ))‖) + (‖N (H (N ψ))‖ + ‖H (N (N ψ))‖) :=
        add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
    _ ≤ _ := by nlinarith

theorem h42_fl_iii {n : ℕ} {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}
    (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (x : fullDom n) :
    |(inner ℂ (x : FermiFock n)
        (dcommOp (smFermiHam hD M z) (smFermiN om c0) (x : FermiFock n)) : ℂ).re|
      ≤ (4 * smFermiBound hD M z * smFermiOm om c0 ^ 2)
        * ‖smFermiN om c0 (x : FermiFock n)‖ ^ 2 := by
  have hB := h42_bound_nonneg hD M z
  have hO := h42_Om_ge hom hc0
  have hD' := h42_dcomm_le (h42_ham_le hD M z) (h42_N_le hom hc0) hB (by linarith) (x : FermiFock n)
  have hge := h42_N_ge hom hc0 (x : FermiFock n)
  have hnv := norm_nonneg (x : FermiFock n)
  calc _ ≤ ‖(inner ℂ (x : FermiFock n) (dcommOp (smFermiHam hD M z) (smFermiN om c0) (x : FermiFock n)) : ℂ)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ‖(x : FermiFock n)‖ * ‖dcommOp (smFermiHam hD M z) (smFermiN om c0) (x : FermiFock n)‖ := norm_inner_le_norm _ _
    _ ≤ ‖(x : FermiFock n)‖ * (4 * smFermiBound hD M z * smFermiOm om c0 ^ 2 * ‖(x : FermiFock n)‖) :=
        mul_le_mul_of_nonneg_left hD' hnv
    _ = (4 * smFermiBound hD M z * smFermiOm om c0 ^ 2) * ‖(x : FermiFock n)‖ ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem solution (d : Finset (Fin n) → ℝ) (ψ : FermiFock n) :
    ‖diagOp d ψ‖ ^ 2 = ∑ S : Finset (Fin n), (d S) ^ 2 * ‖ψ S‖ ^ 2 := by
  exact h42_diag_normSq d ψ

