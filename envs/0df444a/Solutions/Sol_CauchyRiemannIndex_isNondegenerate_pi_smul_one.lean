-- Prove2me | solution 1 for CauchyRiemannIndex.isNondegenerate_pi_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-20T15:44:50.543411+00:00
-- url     : https://prove2.me/submissions/e5e9d8b7-2de4-4440-af9c-a608ed8b765d

import Definitions.Def_CauchyRiemannIndex_Setting
import Definitions.Def_ConleyZehnder_Setting
import Mathlib.Analysis.Calculus.Deriv.Prod
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul

open Matrix

/-!
# Entrywise algebra of the block-diagonal sum `ConleyZehnder.diamond`
-/


namespace CRIFD

/-- The coordinate equivalence used by `ConleyZehnder.diamond`. -/
abbrev dE (m₁ m₂ : ℕ) :
    ((Fin m₁ ⊕ Fin m₁) ⊕ (Fin m₂ ⊕ Fin m₂)) ≃ (Fin (m₁ + m₂) ⊕ Fin (m₁ + m₂)) :=
  (Equiv.sumSumSumComm (Fin m₁) (Fin m₁) (Fin m₂) (Fin m₂)).trans
    (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

variable {m₁ m₂ : ℕ}

lemma diamond_eq (A : CauchyRiemannIndex.Mat m₁) (B : CauchyRiemannIndex.Mat m₂) :
    ConleyZehnder.diamond A B = Matrix.reindex (dE m₁ m₂) (dE m₁ m₂) (Matrix.fromBlocks A 0 0 B) :=
  rfl

lemma diamond_apply_dE (A : CauchyRiemannIndex.Mat m₁) (B : CauchyRiemannIndex.Mat m₂) (a b) :
    ConleyZehnder.diamond A B (dE m₁ m₂ a) (dE m₁ m₂ b) = Matrix.fromBlocks A 0 0 B a b := by
  rw [diamond_eq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

/-- Every entry of `A ⋄ B` is an entry of `A`, an entry of `B`, or `0`, at positions that do not
depend on `A` and `B`. -/
lemma diamond_entry (i j : Fin (m₁ + m₂) ⊕ Fin (m₁ + m₂)) :
    (∃ a b, ∀ (A : CauchyRiemannIndex.Mat m₁) (B : CauchyRiemannIndex.Mat m₂),
        ConleyZehnder.diamond A B i j = A a b) ∨
      (∃ a b, ∀ (A : CauchyRiemannIndex.Mat m₁) (B : CauchyRiemannIndex.Mat m₂),
        ConleyZehnder.diamond A B i j = B a b) ∨
      (∀ (A : CauchyRiemannIndex.Mat m₁) (B : CauchyRiemannIndex.Mat m₂),
        ConleyZehnder.diamond A B i j = 0) := by
  obtain ⟨a, rfl⟩ := (dE m₁ m₂).surjective i
  obtain ⟨b, rfl⟩ := (dE m₁ m₂).surjective j
  rcases a with a | a <;> rcases b with b | b
  · exact Or.inl ⟨a, b, fun A B => by rw [diamond_apply_dE]; rfl⟩
  · exact Or.inr (Or.inr fun A B => by rw [diamond_apply_dE]; rfl)
  · exact Or.inr (Or.inr fun A B => by rw [diamond_apply_dE]; rfl)
  · exact Or.inr (Or.inl ⟨a, b, fun A B => by rw [diamond_apply_dE]; rfl⟩)

lemma continuous_diamond {X : Type*} [TopologicalSpace X] {f : X → CauchyRiemannIndex.Mat m₁}
    {g : X → CauchyRiemannIndex.Mat m₂} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => ConleyZehnder.diamond (f x) (g x) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases diamond_entry (m₁ := m₁) (m₂ := m₂) i j with ⟨a, b, h⟩ | ⟨a, b, h⟩ | h
  · simp only [h]; exact (continuous_apply b).comp ((continuous_apply a).comp hf)
  · simp only [h]; exact (continuous_apply b).comp ((continuous_apply a).comp hg)
  · simp only [h]; exact continuous_const

lemma abs_sub_diamond_le (A A' : CauchyRiemannIndex.Mat m₁) (B B' : CauchyRiemannIndex.Mat m₂)
    {ε : ℝ} (hε : 0 ≤ ε) (hA : ∀ i j, |A i j - A' i j| ≤ ε) (hB : ∀ i j, |B i j - B' i j| ≤ ε)
    (i j) : |ConleyZehnder.diamond A B i j - ConleyZehnder.diamond A' B' i j| ≤ ε := by
  rcases diamond_entry (m₁ := m₁) (m₂ := m₂) i j with ⟨a, b, h⟩ | ⟨a, b, h⟩ | h
  · rw [h, h]; exact hA a b
  · rw [h, h]; exact hB a b
  · rw [h, h, sub_zero, abs_zero]; exact hε

lemma diamond_mul (A A' : CauchyRiemannIndex.Mat m₁) (B B' : CauchyRiemannIndex.Mat m₂) :
    ConleyZehnder.diamond (A * A') (B * B') =
      ConleyZehnder.diamond A B * ConleyZehnder.diamond A' B' := by
  rw [diamond_eq, diamond_eq, diamond_eq, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

lemma diamond_transpose (A : CauchyRiemannIndex.Mat m₁) (B : CauchyRiemannIndex.Mat m₂) :
    (ConleyZehnder.diamond A B)ᵀ = ConleyZehnder.diamond Aᵀ Bᵀ := by
  rw [diamond_eq, diamond_eq, Matrix.transpose_reindex, Matrix.fromBlocks_transpose]
  simp

lemma diamond_one : ConleyZehnder.diamond (1 : CauchyRiemannIndex.Mat m₁)
    (1 : CauchyRiemannIndex.Mat m₂) = 1 := by
  rw [diamond_eq, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

lemma diamond_sub (A A' : CauchyRiemannIndex.Mat m₁) (B B' : CauchyRiemannIndex.Mat m₂) :
    ConleyZehnder.diamond (A - A') (B - B') =
      ConleyZehnder.diamond A B - ConleyZehnder.diamond A' B' := by
  ext i j
  rw [Matrix.sub_apply]
  rcases diamond_entry (m₁ := m₁) (m₂ := m₂) i j with ⟨a, b, h⟩ | ⟨a, b, h⟩ | h
  · rw [h, h, h]; rfl
  · rw [h, h, h]; rfl
  · rw [h, h, h, sub_zero]

lemma det_diamond (A : CauchyRiemannIndex.Mat m₁) (B : CauchyRiemannIndex.Mat m₂) :
    (ConleyZehnder.diamond A B).det = A.det * B.det := by
  rw [diamond_eq, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

lemma J_eq_diamond :
    CauchyRiemannIndex.J₀ (m₁ + m₂) =
      ConleyZehnder.diamond (CauchyRiemannIndex.J₀ m₁) (CauchyRiemannIndex.J₀ m₂) := by
  ext i j
  obtain ⟨a, rfl⟩ := (dE m₁ m₂).surjective i
  obtain ⟨b, rfl⟩ := (dE m₁ m₂).surjective j
  rw [diamond_apply_dE]
  rcases a with (a | a) | (a | a) <;> rcases b with (b | b) | (b | b) <;>
    simp [Matrix.J, Matrix.one_apply]
  all_goals
    intro h
    have := congrArg Fin.val h
    simp at this
    omega

lemma hasDerivAt_mat_iff {m : ℕ} {f : ℝ → CauchyRiemannIndex.Mat m} {f' : CauchyRiemannIndex.Mat m}
    {t : ℝ} : HasDerivAt f f' t ↔ ∀ i j, HasDerivAt (fun s => f s i j) (f' i j) t := by
  constructor
  · intro h i j
    exact hasDerivAt_pi.1 (hasDerivAt_pi.1 h i) j
  · intro h
    exact hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => h i j

lemma hasDerivAt_diamond {f : ℝ → CauchyRiemannIndex.Mat m₁} {g : ℝ → CauchyRiemannIndex.Mat m₂}
    {f' : CauchyRiemannIndex.Mat m₁} {g' : CauchyRiemannIndex.Mat m₂} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => ConleyZehnder.diamond (f s) (g s)) (ConleyZehnder.diamond f' g') t := by
  rw [hasDerivAt_mat_iff] at hf hg ⊢
  intro i j
  rcases diamond_entry (m₁ := m₁) (m₂ := m₂) i j with ⟨a, b, h⟩ | ⟨a, b, h⟩ | h
  · simp only [h]; exact hf a b
  · simp only [h]; exact hg a b
  · simp only [h]; exact hasDerivAt_const _ _

end CRIFD

/-!
# The constant loop `π · Id` is nondegenerate
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- The fundamental solution `cos(πt) Id + sin(πt) J₀` of the constant loop `π · Id`. -/
lemma crif_fund_pi (m : ℕ) :
    IsFundamentalSolution (fun _ : ℝ => Real.pi • (1 : Mat m))
      (fun t => Real.cos (Real.pi * t) • (1 : Mat m) + Real.sin (Real.pi * t) • J₀ m) := by
  refine ⟨by simp, fun t => ?_⟩
  have hl : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi t := by
    simpa using (hasDerivAt_id t).const_mul Real.pi
  have hJ : J₀ m * J₀ m = -1 := Matrix.J_squared (Fin m) ℝ
  have key : J₀ m * (Real.pi • (1 : Mat m)) *
      (Real.cos (Real.pi * t) • (1 : Mat m) + Real.sin (Real.pi * t) • J₀ m) =
      (-Real.sin (Real.pi * t) * Real.pi) • (1 : Mat m) + (Real.cos (Real.pi * t) * Real.pi) • J₀ m := by
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hJ]
    module
  rw [key, CRIFD.hasDerivAt_mat_iff]
  intro i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact ((hl.cos).mul_const _).add ((hl.sin).mul_const _)

theorem isNondegenerate_pi_smul_one_aux (m : ℕ) :
    IsSymLoop (fun _ : ℝ => Real.pi • (1 : Mat m)) ∧
      IsNondegenerate (fun _ : ℝ => Real.pi • (1 : Mat m)) := by
  refine ⟨⟨continuous_const, fun _ => rfl, fun _ => (Matrix.isSymm_one).smul Real.pi⟩, ?_⟩
  intro Ψ hΨ
  obtain ⟨Φ, _, huniq⟩ := fundamentalSolution_existsUnique m (fun _ : ℝ => Real.pi • (1 : Mat m))
    continuous_const
  have hE : Ψ = fun t => Real.cos (Real.pi * t) • (1 : Mat m) + Real.sin (Real.pi * t) • J₀ m :=
    (huniq Ψ hΨ).trans (huniq _ (crif_fund_pi m)).symm
  rw [hE]
  have h1 : (1 : Mat m) - (Real.cos (Real.pi * 1) • (1 : Mat m) + Real.sin (Real.pi * 1) • J₀ m) =
      (2 : ℝ) • (1 : Mat m) := by
    simp only [mul_one, Real.cos_pi, Real.sin_pi, zero_smul, add_zero]
    module
  rw [h1, Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ two_ne_zero

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (m : ℕ) :
    IsSymLoop (fun _ : ℝ => Real.pi • (1 : Mat m)) ∧
      IsNondegenerate (fun _ : ℝ => Real.pi • (1 : Mat m)) :=
  CauchyRiemannIndex.isNondegenerate_pi_smul_one_aux m
