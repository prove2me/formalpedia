-- Prove2me | solution 1 for EquivPosMaps.TwoPositive.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:19:43.703343+00:00
-- url     : https://prove2.me/submissions/8c00594a-cd74-4c08-a5c8-ec88aca24a96

import Mathlib
import Definitions.Def_EquivPosMaps_TwoPositive_Basic

open scoped Matrix Kronecker ComplexOrder
open EquivPosMaps.TwoPositive Matrix

lemma permUX {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    (Matrix.of fun a b => if a = σ b then (1:ℂ) else 0) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.star_apply, Matrix.one_apply]
  have : ∀ c, (if a = σ c then (1:ℂ) else 0) * star (if b = σ c then (1:ℂ) else 0) =
      if c = σ.symm a then (if a = b then 1 else 0) else 0 := by
    intro c
    by_cases h1 : c = σ.symm a
    · subst h1; simp [eq_comm]
    · have : a ≠ σ c := fun h => h1 (by rw [h]; simp)
      simp [this, h1]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma permConjX {d : ℕ} (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    (Matrix.of fun a b => if a = σ b then (1:ℂ) else 0) * Matrix.single i i 1 *
      star (Matrix.of fun a b => if a = σ b then (1:ℂ) else 0) = Matrix.single (σ i) (σ i) 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.star_apply, Matrix.single_apply]
  simp [Finset.sum_ite, ite_and, mul_ite]
  rcases eq_or_ne b (σ i) with rfl | h1 <;> rcases eq_or_ne a (σ i) with rfl | h2 <;>
    simp_all [eq_comm]

theorem solution (d₁ d₂ : ℕ) [NeZero d₁]
    (Φ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] Matrix (Fin d₂) (Fin d₂) ℂ)
    (hequiv : ∀ U : Matrix.unitaryGroup (Fin d₁) ℂ,
      ∃ V : Matrix (Fin d₂) (Fin d₂) ℂ, ∀ X : Matrix (Fin d₁) (Fin d₁) ℂ,
        Φ ((U : Matrix (Fin d₁) (Fin d₁) ℂ) * X * star (U : Matrix (Fin d₁) (Fin d₁) ℂ)) =
          V * Φ X * Vᴴ)
    (hunit : (Φ (Matrix.single 0 0 1)).PosSemidef) :
    IsPositiveMap Φ := by
  intro X hX
  have hspec := hX.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set W := hX.1.eigenvectorUnitary
  set e := hX.1.eigenvalues
  have hdiag : diagonal (RCLike.ofReal ∘ e : Fin d₁ → ℂ) =
      ∑ i, ((e i : ℝ) : ℂ) • Matrix.single i i (1:ℂ) := by
    ext a b
    simp [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.single_apply]
    by_cases h : a = b
    · subst h; simp
    · simp only [if_neg h]; symm; apply Finset.sum_eq_zero; intro c _
      rw [if_neg]; rintro ⟨rfl, rfl⟩; exact h rfl
  have hX' : X = ∑ i, ((e i : ℝ) : ℂ) •
      ((W : Matrix (Fin d₁) (Fin d₁) ℂ) * Matrix.single i i 1 * star (W : Matrix (Fin d₁) (Fin d₁) ℂ)) := by
    conv_lhs => rw [hspec]
    rw [hdiag, Matrix.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hterm : ∀ i, (Φ ((W : Matrix (Fin d₁) (Fin d₁) ℂ) * Matrix.single i i 1 *
      star (W : Matrix (Fin d₁) (Fin d₁) ℂ))).PosSemidef := by
    intro i
    let σ : Equiv.Perm (Fin d₁) := Equiv.swap 0 i
    let Pm : Matrix.unitaryGroup (Fin d₁) ℂ := ⟨_, permUX σ⟩
    have hσ : σ 0 = i := by simp [σ]
    have e1 : Matrix.single i i (1:ℂ) = (Pm : Matrix (Fin d₁) (Fin d₁) ℂ) * Matrix.single 0 0 1 *
        star (Pm : Matrix (Fin d₁) (Fin d₁) ℂ) := by
      rw [show (Pm : Matrix (Fin d₁) (Fin d₁) ℂ) = Matrix.of fun a b => if a = σ b then (1:ℂ) else 0 from rfl,
        permConjX, hσ]
    obtain ⟨V, hV⟩ := hequiv (W * Pm)
    rw [e1]
    have : (W : Matrix (Fin d₁) (Fin d₁) ℂ) * ((Pm : Matrix (Fin d₁) (Fin d₁) ℂ) * Matrix.single 0 0 1 *
        star (Pm : Matrix (Fin d₁) (Fin d₁) ℂ)) * star (W : Matrix (Fin d₁) (Fin d₁) ℂ) =
        ((W * Pm : Matrix.unitaryGroup (Fin d₁) ℂ) : Matrix (Fin d₁) (Fin d₁) ℂ) * Matrix.single 0 0 1 *
          star ((W * Pm : Matrix.unitaryGroup (Fin d₁) ℂ) : Matrix (Fin d₁) (Fin d₁) ℂ) := by
      simp only [Matrix.UnitaryGroup.mul_val, star_mul, Matrix.mul_assoc]
    rw [this, hV]
    exact hunit.mul_mul_conjTranspose_same V
  rw [hX', map_sum]
  apply Matrix.posSemidef_sum
  intro i _
  rw [map_smul]
  exact (hterm i).smul (by exact_mod_cast hX.eigenvalues_nonneg i)
