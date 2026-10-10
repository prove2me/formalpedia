-- Prove2me | solution 1 for ConleyZehnder.spStar_exists_path_to_W
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T20:26:54.653105+00:00
-- url     : https://prove2.me/submissions/d9fecf1a-2a5d-44c1-8ee8-2d4e6d403c5b

import Theorems.Thm_ConleyZehnder_hamiltonian_joinedIn_cube
import Theorems.Thm_ConleyZehnder_hamiltonian_cube_joinedIn_normal

/-! Reduction of `spStar_exists_path_to_W` to the two statements on Hamiltonian matrices, via the
Cayley transform `X ↦ (X + 1)(X - 1)⁻¹`. -/

open ConleyZehnder Matrix

namespace CZ8



variable {n : ℕ}

/-- Hamiltonian matrices without eigenvalue `1`. -/
def HamStar (n : ℕ) : Set (Mat n) := {X | X * J₀ n + J₀ n * Xᵀ = 0 ∧ (1 - X).det ≠ 0}

/-- The Cayley transform `(X + 1)(X - 1)⁻¹`. -/
noncomputable def cay (X : Mat n) : Mat n := (X + 1) * (X - 1)⁻¹

lemma det_sub_one_ne_zero {X : Mat n} (h : (1 - X).det ≠ 0) : (X - 1).det ≠ 0 := by
  have : X - 1 = -(1 - X) := by abel
  rw [this, Matrix.det_neg]
  simp [Fintype.card_sum, h]

lemma isUnit_det_sub_one {X : Mat n} (h : (1 - X).det ≠ 0) : IsUnit (X - 1).det :=
  isUnit_iff_ne_zero.2 (det_sub_one_ne_zero h)

lemma one_sub_cay {X : Mat n} (h : (1 - X).det ≠ 0) : 1 - cay X = (-2 : ℝ) • (X - 1)⁻¹ := by
  have hu := isUnit_det_sub_one h
  calc 1 - cay X = (X - 1) * (X - 1)⁻¹ - (X + 1) * (X - 1)⁻¹ := by
        rw [Matrix.mul_nonsing_inv _ hu]; rfl
    _ = (X - 1 - (X + 1)) * (X - 1)⁻¹ := by rw [← Matrix.sub_mul]
    _ = ((-2 : ℝ) • (1 : Mat n)) * (X - 1)⁻¹ := by
        congr 1; rw [show X - 1 - (X + 1) = -((1 : Mat n) + 1) by abel]
        rw [neg_smul, two_smul]
    _ = (-2 : ℝ) • (X - 1)⁻¹ := by rw [Matrix.smul_mul, Matrix.one_mul]

lemma det_one_sub_cay_ne_zero {X : Mat n} (h : (1 - X).det ≠ 0) : (1 - cay X).det ≠ 0 := by
  rw [one_sub_cay h, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (inv_ne_zero (det_sub_one_ne_zero h))

/-- `(X - 1) cay X = X + 1`. -/
lemma sub_one_mul_cay {X : Mat n} (h : (1 - X).det ≠ 0) : (X - 1) * cay X = X + 1 := by
  have hu := isUnit_det_sub_one h
  have hc : (X - 1) * (X + 1) = (X + 1) * (X - 1) := by noncomm_ring
  unfold cay
  rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

lemma cay_eq_of {X W : Mat n} (h : (1 - X).det ≠ 0) (hW : (X - 1) * W = X + 1) : cay X = W := by
  have hu := isUnit_det_sub_one h
  have e : (X - 1) * cay X = (X - 1) * W := by rw [sub_one_mul_cay h, hW]
  have := congrArg (fun M => (X - 1)⁻¹ * M) e
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul] using this

lemma cay_mem_symplectic {X : Mat n} (hH : X * J₀ n + J₀ n * Xᵀ = 0) (h : (1 - X).det ≠ 0) :
    cay X ∈ symplecticGroup (Fin n) ℝ := by
  rw [SymplecticGroup.mem_iff]
  set Q := X - 1 with hQdef
  have hu : IsUnit Q.det := isUnit_det_sub_one h
  have hut : IsUnit Qᵀ.det := by rwa [Matrix.det_transpose]
  have hQ : Q * cay X = X + 1 := sub_one_mul_cay h
  have key : Q * (cay X * J₀ n * (cay X)ᵀ) * Qᵀ = Q * J₀ n * Qᵀ := by
    have e1 : Q * (cay X * J₀ n * (cay X)ᵀ) * Qᵀ = (Q * cay X) * J₀ n * (Q * cay X)ᵀ := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e1, hQ, hQdef]
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one]
    have : (X + 1) * J₀ n * (Xᵀ + 1) - (X - 1) * J₀ n * (Xᵀ - 1)
        = (2 : ℝ) • (X * J₀ n + J₀ n * Xᵀ) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.one_mul, two_smul]
      abel
    rw [hH, smul_zero] at this
    exact sub_eq_zero.1 this
  have := congrArg (fun M => Q⁻¹ * M * Qᵀ⁻¹) key
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul] at this
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hut] using this

lemma cay_mem_spStar {X : Mat n} (hX : X ∈ HamStar n) : cay X ∈ SpStar n :=
  ⟨cay_mem_symplectic hX.1 hX.2, det_one_sub_cay_ne_zero hX.2⟩

lemma cay_mem_hamStar {A : Mat n} (hA : A ∈ SpStar n) : cay A ∈ HamStar n := by
  refine ⟨?_, det_one_sub_cay_ne_zero hA.2⟩
  have hS : A * J₀ n * Aᵀ = J₀ n := (SymplecticGroup.mem_iff).1 hA.1
  set Q := A - 1 with hQdef
  have hu : IsUnit Q.det := isUnit_det_sub_one hA.2
  have hut : IsUnit Qᵀ.det := by rwa [Matrix.det_transpose]
  have hQ : Q * cay A = A + 1 := sub_one_mul_cay hA.2
  have key : Q * (cay A * J₀ n + J₀ n * (cay A)ᵀ) * Qᵀ = 0 := by
    have e1 : Q * (cay A * J₀ n + J₀ n * (cay A)ᵀ) * Qᵀ
        = (Q * cay A) * J₀ n * Qᵀ + Q * J₀ n * (Q * cay A)ᵀ := by
      simp [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [e1, hQ, hQdef]
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one]
    have : (A + 1) * J₀ n * (Aᵀ - 1) + (A - 1) * J₀ n * (Aᵀ + 1)
        = (2 : ℝ) • (A * J₀ n * Aᵀ - J₀ n) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.one_mul, two_smul]
      abel
    rw [this, hS, sub_self, smul_zero]
  have := congrArg (fun M => Q⁻¹ * M * Qᵀ⁻¹) key
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
    Matrix.zero_mul, Matrix.mul_zero] at this
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hut] using this

lemma cay_cay {A : Mat n} (h : (1 - A).det ≠ 0) : cay (cay A) = A := by
  have hu : IsUnit (A - 1).det := isUnit_det_sub_one h
  have h2 : (1 - cay A).det ≠ 0 := det_one_sub_cay_ne_zero h
  apply cay_eq_of h2
  have hm : cay A - 1 = (2 : ℝ) • (A - 1)⁻¹ := by
    rw [show cay A - 1 = -(1 - cay A) by abel, one_sub_cay h, neg_smul, neg_neg]
  have hL : (A - 1)⁻¹ * A = 1 + (A - 1)⁻¹ := by
    rw [show (A - 1)⁻¹ * A = (A - 1)⁻¹ * ((A - 1) + 1) by rw [sub_add_cancel]]
    rw [Matrix.mul_add, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  rw [hm, Matrix.smul_mul, hL, show cay A + 1 = (cay A - 1) + (1 + 1) by abel, hm,
    smul_add, two_smul ℝ (1 : Mat n)]
  abel

lemma continuousOn_cay : ContinuousOn (cay (n := n)) {X | (1 - X).det ≠ 0} := by
  have hs : Continuous fun X : Mat n => X - 1 := continuous_id.sub continuous_const
  have hp : Continuous fun X : Mat n => X + 1 := continuous_id.add continuous_const
  have hd : Continuous fun X : Mat n => (X - 1).det := hs.matrix_det
  have hinv : ContinuousOn (fun X : Mat n => ((X - 1).det)⁻¹) {X | (1 - X).det ≠ 0} :=
    hd.continuousOn.inv₀ fun X hX => det_sub_one_ne_zero hX
  have hadj : Continuous fun X : Mat n => (X - 1).adjugate := hs.matrix_adjugate
  refine (hp.continuousOn.mul (hinv.smul hadj.continuousOn)).congr ?_
  intro X _
  simp [cay, Matrix.inv_def, Ring.inverse_eq_inv']

lemma cay_zero : cay (0 : Mat n) = Wplus n := by
  apply cay_eq_of (by simp)
  simp [Wplus]

/-- The Hamiltonian counterpart of `W⁻`. -/
noncomputable def Yminus (n : ℕ) : Mat n :=
  Matrix.diagonal (Sum.elim (fun j : Fin n => if j.val = 0 then (3 : ℝ) else 0)
    (fun j : Fin n => if j.val = 0 then (-3 : ℝ) else 0))

lemma det_one_sub_Yminus : (1 - Yminus n).det ≠ 0 := by
  unfold Yminus
  rw [show (1 : Mat n) = Matrix.diagonal 1 from rfl, Matrix.diagonal_sub, Matrix.det_diagonal]
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rcases i with j | j <;> by_cases hj : j.val = 0 <;> simp [hj] <;> norm_num

lemma cay_Yminus : cay (Yminus n) = Wminus n := by
  apply cay_eq_of det_one_sub_Yminus
  unfold Yminus Wminus
  rw [show (1 : Mat n) = Matrix.diagonal 1 from rfl, Matrix.diagonal_sub, Matrix.diagonal_add,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rcases i with j | j <;> by_cases hj : j.val = 0 <;> simp [hj] <;> norm_num

lemma Yminus_ham : Yminus n * J₀ n + J₀ n * (Yminus n)ᵀ = 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Yminus, Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal_apply,
      Matrix.one_apply] <;>
    (rcases eq_or_ne i j with rfl | h <;> simp [*] <;> split_ifs <;> norm_num)

lemma Yminus_mem : Yminus n ∈ HamStar n := ⟨Yminus_ham, det_one_sub_Yminus⟩

lemma zero_mem_hamStar : (0 : Mat n) ∈ HamStar n := ⟨by simp, by simp⟩

/-- Transport: a path in `HamStar` from `cay A` to `0` or `Yminus` gives the target. -/
theorem spStar_path_of_hamStar {A : Mat n} (hA : A ∈ SpStar n)
    (h : JoinedIn (HamStar n) (cay A) 0 ∨ JoinedIn (HamStar n) (cay A) (Yminus n)) :
    ∃ χ : C(unitInterval, Mat n), χ 0 = A ∧ (∀ t, χ t ∈ SpStar n) ∧
      (χ 1 = Wplus n ∨ χ 1 = Wminus n) := by
  have hmap : ∀ {Y : Mat n}, JoinedIn (HamStar n) (cay A) Y →
      JoinedIn (SpStar n) A (cay Y) := by
    intro Y hY
    have := hY.map_continuousOn (f := cay) (continuousOn_cay.mono fun X hX => hX.2)
    rw [cay_cay hA.2] at this
    exact this.mono (Set.image_subset_iff.2 fun X hX => cay_mem_spStar hX)
  rcases h with h | h
  · have hj := hmap h
    rw [cay_zero] at hj
    exact ⟨hj.somePath, by simp, hj.somePath_mem, Or.inl (by simp)⟩
  · have hj := hmap h
    rw [cay_Yminus] at hj
    exact ⟨hj.somePath, by simp, hj.somePath_mem, Or.inr (by simp)⟩

end CZ8

theorem solution {n : ℕ} (A : Mat n) (hA : A ∈ SpStar n) :
    ∃ χ : C(unitInterval, Mat n), χ 0 = A ∧ (∀ t, χ t ∈ SpStar n) ∧
      (χ 1 = Wplus n ∨ χ 1 = Wminus n) := by
  have hX := CZ8.cay_mem_hamStar hA
  obtain ⟨Y, hY, h3, hXY⟩ := hamiltonian_joinedIn_cube (CZ8.cay A) hX.1 hX.2
  refine CZ8.spStar_path_of_hamStar hA ?_
  rcases hamiltonian_cube_joinedIn_normal Y hY h3 with h | h
  · exact Or.inl (hXY.trans h)
  · exact Or.inr (hXY.trans h)
