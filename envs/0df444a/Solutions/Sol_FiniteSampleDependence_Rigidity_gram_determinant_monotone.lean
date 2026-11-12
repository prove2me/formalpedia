-- Prove2me | solution 1 for FiniteSampleDependence.Rigidity.gram_determinant_monotone
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:00:25.506665+00:00
-- url     : https://prove2.me/submissions/8c9d9d7e-84ef-45db-a4ab-8472f2f584e1

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_PolynomialAlgebra

section
set_option autoImplicit false

namespace FiniteSampleDependence.Dev.Gram

open FiniteSampleDependence.Rigidity Matrix MvPolynomial

theorem gram_homog (n m : ℕ) : (gramPoly n m).IsHomogeneous (2 * n) := by
  unfold gramPoly
  rw [Matrix.det_apply]
  have : 2 * n = ∑ _i : Fin n, 2 := by simp [mul_comm]
  rw [this]
  apply IsHomogeneous.sum
  intro σ _
  have h : ∀ i : Fin n, ((genericMatrix n m * (genericMatrix n m)ᵀ) (σ i) i).IsHomogeneous 2 := by
    intro i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, genericMatrix, Matrix.mvPolynomialX_apply]
    have : (2:ℕ) = 1 + 1 := rfl
    rw [this]
    apply IsHomogeneous.sum
    intro k _
    exact (isHomogeneous_X _ _).mul (isHomogeneous_X _ _)
  have hp := IsHomogeneous.prod Finset.univ (fun i : Fin n => (genericMatrix n m * (genericMatrix n m)ᵀ) (σ i) i) (fun _ => 2) (fun i _ => h i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · rw [h1]; simpa using hp
  · rw [h1]; simpa using hp.neg

theorem det_T_sq_le {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsColumnStochastic T) :
    T.det ^ 2 ≤ 1 := by
  have key : |T.det| ≤ 1 := by
    rw [Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, T (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin n), |Equiv.Perm.sign σ • ∏ i, T (σ i) i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, T (σ i) i := by
          apply Finset.sum_congr rfl
          intro σ _
          have hp : 0 ≤ ∏ i, T (σ i) i := Finset.prod_nonneg (fun i _ => hT.1 _ _)
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> rw [h1] <;>
            simp [abs_of_nonneg hp]
      _ ≤ ∑ f ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (Fin n))), ∏ i, T (f i) i := by
          have hinj : Function.Injective (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n)) :=
            fun a b h => Equiv.ext (fun x => congrFun h x)
          rw [← Finset.sum_image (f := fun f : Fin n → Fin n => ∏ i, T (f i) i)
            (s := Finset.univ) (g := fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n))
            (fun a _ b _ h => hinj h)]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro f _
            simp
          · intro f _ _
            exact Finset.prod_nonneg (fun i _ => hT.1 _ _)
      _ = 1 := by
          rw [← Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin n)))
            (fun i j => T j i)]
          simp [hT.2]
  have := sq_le_one_iff_abs_le_one T.det
  exact this.mpr key

theorem gram_nonneg {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℝ) : 0 ≤ (U * Uᵀ).det := by
  have := Matrix.posSemidef_self_mul_conjTranspose U
  simpa using this.det_nonneg

theorem gram_lfdpi (n m : ℕ) : LFDPI (polyFun (gramPoly n m)) := by
  intro U _ T hT
  rw [polyFun_gramPoly, polyFun_gramPoly, Matrix.transpose_mul]
  have e : T * U * (Uᵀ * Tᵀ) = T * (U * Uᵀ) * Tᵀ := by simp [Matrix.mul_assoc]
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  · have h1 := det_T_sq_le T hT
    have h2 := gram_nonneg U
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  
theorem gram_iz (n m : ℕ) (hn : 2 ≤ n) : IZ (polyFun (gramPoly n m)) := by
  intro U _ hr
  rw [polyFun_gramPoly]
  by_contra hne
  have hu : IsUnit (U * Uᵀ) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hne
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 : (U * Uᵀ).rank ≤ U.rank := Matrix.rank_mul_le_left _ _
  simp only [Fintype.card_fin] at h1
  omega

theorem exists_point {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    ∃ U ∈ simplex n m, (U * Uᵀ).det ≠ 0 := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  refine ⟨Matrix.of fun i α => if (i:ℕ) = α then 1 / (n:ℝ) else 0, ⟨?_, ?_⟩, ?_⟩
  · intro i α; simp only [Matrix.of_apply]; split_ifs <;> positivity
  · unfold tau
    have : ∀ i : Fin n, ∑ α : Fin m, (Matrix.of fun (i : Fin n) (α : Fin m) =>
        if (i:ℕ) = α then 1 / (n:ℝ) else 0) i α = 1 / (n:ℝ) := by
      intro i
      rw [Finset.sum_eq_single (Fin.castLE hnm i)]
      · simp
      · intro b _ hb
        simp only [Matrix.of_apply]
        rw [if_neg]
        intro h
        apply hb
        ext; simp [h]
      · simp
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp
    field_simp
  · have : (Matrix.of fun (i : Fin n) (α : Fin m) =>
        if (i:ℕ) = α then 1 / (n:ℝ) else 0) * (Matrix.of fun (i : Fin n) (α : Fin m) =>
        if (i:ℕ) = α then 1 / (n:ℝ) else 0)ᵀ = (1 / (n:ℝ))^2 • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply,
        Matrix.one_apply]
      rw [Finset.sum_eq_single (Fin.castLE hnm i)]
      · by_cases h : i = j
        · subst h; simp [sq]
        · have : ¬ ((i:ℕ) = j) := fun h' => h (Fin.ext h')
          have this' : ¬ ((j:ℕ) = i) := fun h' => this h'.symm
          simp [h, this']
      · intro b _ hb
        have : ¬ ((i:ℕ) = b) := by
          intro h; apply hb; ext; simp [h]
        simp [this]
      · simp
    rw [this, Matrix.det_smul]
    simp [hn0]

end FiniteSampleDependence.Dev.Gram

namespace FiniteSampleDependence.Rigidity

open FiniteSampleDependence.Dev.Gram

theorem chk_gram_determinant_monotone {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    gramPoly n m ≠ 0 ∧
    (∃ U ∈ simplex n m, polyFun (gramPoly n m) U ≠ 0) ∧
    (gramPoly n m).totalDegree = 2 * n ∧
    LFDPI (polyFun (gramPoly n m)) ∧
    IZ (polyFun (gramPoly n m)) := by
  have hex : ∃ U ∈ simplex n m, polyFun (gramPoly n m) U ≠ 0 := by
    obtain ⟨U, hU, h⟩ := exists_point hn hnm
    exact ⟨U, hU, by rwa [polyFun_gramPoly]⟩
  have hne : gramPoly n m ≠ 0 := by
    obtain ⟨U, _, h⟩ := hex
    intro h0
    apply h
    simp [h0, polyFun]
  exact ⟨hne, hex, (gram_homog n m).totalDegree hne, gram_lfdpi n m, gram_iz n m hn⟩

end FiniteSampleDependence.Rigidity

end

theorem solution : type_of% @FiniteSampleDependence.Rigidity.chk_gram_determinant_monotone := @FiniteSampleDependence.Rigidity.chk_gram_determinant_monotone
