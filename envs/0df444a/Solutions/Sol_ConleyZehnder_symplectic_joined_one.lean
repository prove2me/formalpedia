-- Prove2me | solution 1 for ConleyZehnder.symplectic_joined_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T21:57:03.118478+00:00
-- url     : https://prove2.me/submissions/d479cb10-06a1-444b-ba06-fe8e64f4a7b8

import Theorems.Thm_ConleyZehnder_spStar_exists_path_to_W
import Theorems.Thm_ConleyZehnder_exists_rotation_mul_mem_spStar

open ConleyZehnder Matrix unitInterval

namespace CZ10J

variable {n : ℕ}

theorem inv_eq (A : Mat n) (hA : IsSymplectic A) : A⁻¹ = -J₀ n * Aᵀ * J₀ n :=
  SymplecticGroup.inv_eq_symplectic_inv A hA

theorem inv_symp (A : Mat n) (hA : IsSymplectic A) : IsSymplectic A⁻¹ := by
  rw [inv_eq A hA]; exact (⟨A, hA⟩⁻¹ : Matrix.symplecticGroup (Fin n) ℝ).2

theorem mul_inv (A : Mat n) (hA : IsSymplectic A) : A * A⁻¹ = 1 := by
  rw [mul_eq_one_comm, inv_eq A hA]
  have := SymplecticGroup.inv_left_mul_aux hA
  rw [← this]; simp only [Matrix.neg_mul]

theorem inv_mul (A : Mat n) (hA : IsSymplectic A) : A⁻¹ * A = 1 :=
  mul_eq_one_comm.mp (mul_inv A hA)

theorem mul_symp {A B : Mat n} (hA : IsSymplectic A) (hB : IsSymplectic B) :
    IsSymplectic (A * B) := Submonoid.mul_mem _ hA hB

/-- Block matrix with diagonal blocks. -/
noncomputable def blk (a b c d : Fin n → ℝ) : Mat n :=
  fromBlocks (diagonal a) (diagonal b) (diagonal c) (diagonal d)

theorem blk_symp (a b c d : Fin n → ℝ) (h : ∀ j, a j * d j - b j * c j = 1) :
    IsSymplectic (blk a b c d) := by
  unfold IsSymplectic blk
  rw [SymplecticGroup.mem_iff]
  simp only [Matrix.J, fromBlocks_transpose, diagonal_transpose, fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.mul_one, zero_add, add_zero,
    diagonal_mul_diagonal]
  congr 1
  · ext i j; by_cases hij : i = j <;> simp [diagonal_apply, hij] <;> ring
  · ext i j; by_cases hij : i = j <;> simp [diagonal_apply, hij]
    · subst hij; linarith [h i]
  · ext i j; by_cases hij : i = j <;> simp [diagonal_apply, hij]
    · subst hij; rw [one_apply_eq]; linarith [h i]
  · ext i j; by_cases hij : i = j <;> simp [diagonal_apply, hij] <;> ring

/-- The rotation `e^{θ J₀} = cos θ · Id + sin θ · J₀`. -/
noncomputable def rot (θ : ℝ) : Mat n := Real.cos θ • (1 : Mat n) + Real.sin θ • J₀ n

theorem rot_eq (θ : ℝ) : rot (n := n) θ = blk (fun _ => Real.cos θ) (fun _ => -Real.sin θ)
    (fun _ => Real.sin θ) (fun _ => Real.cos θ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    by_cases hij : i = j <;> simp [rot, blk, Matrix.J, diagonal_apply, one_apply, hij]

theorem rot_symp (θ : ℝ) : IsSymplectic (rot (n := n) θ) := by
  rw [rot_eq]; exact blk_symp _ _ _ _ fun _ => by nlinarith [Real.sin_sq_add_cos_sq θ]

theorem rot_zero : rot (n := n) 0 = 1 := by simp [rot]

theorem rot_pi : rot (n := n) Real.pi = Wplus n := by simp [rot, Wplus]

theorem continuous_rot {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) :
    Continuous fun x => rot (n := n) (f x) := by
  unfold rot; fun_prop

/-- A path from `W⁻` to `Id` through block matrices with diagonal blocks. -/
noncomputable def wmPath (s : ℝ) : Mat n :=
  blk (fun j => if j.val = 0 then Real.exp ((1 - s) * Real.log 2) else Real.cos (Real.pi * (1 - s)))
    (fun j => if j.val = 0 then 0 else -Real.sin (Real.pi * (1 - s)))
    (fun j => if j.val = 0 then 0 else Real.sin (Real.pi * (1 - s)))
    (fun j => if j.val = 0 then Real.exp ((s - 1) * Real.log 2) else Real.cos (Real.pi * (1 - s)))

theorem wmPath_symp (s : ℝ) : IsSymplectic (wmPath (n := n) s) := by
  refine blk_symp _ _ _ _ fun j => ?_
  by_cases hj : j.val = 0 <;> simp only [hj, if_true, if_false]
  · rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  · nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (1 - s))]

theorem continuous_wmPath : Continuous fun s : ℝ => wmPath (n := n) s := by
  unfold wmPath blk
  refine Continuous.matrix_fromBlocks ?_ ?_ ?_ ?_ <;> refine Continuous.matrix_diagonal ?_ <;>
    refine continuous_pi fun j => ?_ <;> split_ifs <;> fun_prop

theorem wmPath_zero : wmPath (n := n) 0 = Wminus n := by
  ext i j
  have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have h2' : Real.exp (-Real.log 2) = 1 / 2 := by rw [Real.exp_neg, h2]; norm_num
  rcases i with i | i <;> rcases j with j | j <;>
    by_cases hij : i = j <;> simp [wmPath, blk, Wminus, diagonal_apply, hij, h2, h2'] <;>
    split_ifs <;> simp_all

theorem wmPath_one : wmPath (n := n) 1 = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    by_cases hij : i = j <;> simp [wmPath, blk, diagonal_apply, one_apply, hij] <;>
    split_ifs <;> simp

/-- A path of symplectic matrices from `W⁺` or `W⁻` to `Id`. -/
theorem exists_path_W_one (W : Mat n) (hW : W = Wplus n ∨ W = Wminus n) :
    ∃ ω : C(unitInterval, Mat n), ω 0 = W ∧ ω 1 = 1 ∧ ∀ t, IsSymplectic (ω t) := by
  rcases hW with rfl | rfl
  · refine ⟨⟨fun s => rot (Real.pi * (1 - s)), continuous_rot (by fun_prop)⟩, ?_, ?_,
      fun t => rot_symp _⟩
    · show rot (Real.pi * (1 - ((0 : unitInterval) : ℝ))) = _
      simp [rot_pi]
    · show rot (Real.pi * (1 - ((1 : unitInterval) : ℝ))) = _
      simp [rot_zero]
  · refine ⟨⟨fun s => wmPath s, continuous_wmPath.comp continuous_subtype_val⟩, ?_, ?_,
      fun t => wmPath_symp _⟩
    · show wmPath ((0 : unitInterval) : ℝ) = _
      simp [wmPath_zero]
    · show wmPath ((1 : unitInterval) : ℝ) = _
      simp [wmPath_one]

end CZ10J

open CZ10J

theorem solution {n : ℕ} (A : Mat n) (hA : IsSymplectic A) :
    ∃ γ : C(unitInterval, Mat n), γ 0 = 1 ∧ γ 1 = A ∧ ∀ t, IsSymplectic (γ t) := by
  obtain ⟨θ, hQ⟩ := exists_rotation_mul_mem_spStar A hA
  have hrot : rot (n := n) θ = Real.cos θ • (1 : Mat n) + Real.sin θ • J₀ n := rfl
  rw [← hrot] at hQ
  obtain ⟨χ, hχ0, hχs, hχW⟩ := spStar_exists_path_to_W _ hQ
  obtain ⟨ω, hω0, hω1, hωs⟩ := exists_path_W_one (χ 1) hχW
  have hWs : IsSymplectic (χ 1) := (hχs 1).1
  have hRinv : ∀ x : ℝ, (rot (n := n) x)⁻¹ = -J₀ n * (rot x)ᵀ * J₀ n :=
    fun x => inv_eq _ (rot_symp x)
  have hc : Continuous fun s : unitInterval => (rot (n := n) ((s : ℝ) * θ))⁻¹ := by
    simp only [hRinv]
    exact (continuous_const.mul (continuous_rot (by fun_prop)).matrix_transpose).mul
      continuous_const
  refine ⟨⟨fun s => χ (σ s) * (χ 1)⁻¹ * ω (σ s) * (rot ((s : ℝ) * θ))⁻¹, ?_⟩, ?_, ?_, ?_⟩
  · exact (((χ.continuous.comp continuous_symm).mul continuous_const).mul
      (ω.continuous.comp continuous_symm)).mul hc
  · show χ (σ 0) * (χ 1)⁻¹ * ω (σ 0) * (rot (((0 : unitInterval) : ℝ) * θ))⁻¹ = 1
    rw [symm_zero, mul_inv _ hWs, hω1]
    simp [rot_zero]
  · show χ (σ 1) * (χ 1)⁻¹ * ω (σ 1) * (rot (((1 : unitInterval) : ℝ) * θ))⁻¹ = A
    rw [symm_one, hω0, Matrix.mul_assoc (χ 0), inv_mul _ hWs, Matrix.mul_one, hχ0]
    simp only [Set.Icc.coe_one, one_mul]
    rw [Matrix.mul_assoc, mul_inv _ (rot_symp θ), Matrix.mul_one]
  · intro t
    exact mul_symp (mul_symp (mul_symp (hχs _).1 (inv_symp _ hWs)) (hωs _))
      (inv_symp _ (rot_symp _))
