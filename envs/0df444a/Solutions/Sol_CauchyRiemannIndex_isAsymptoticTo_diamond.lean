-- Prove2me | solution 1 for CauchyRiemannIndex.isAsymptoticTo_diamond
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-20T15:44:52.417786+00:00
-- url     : https://prove2.me/submissions/a3eb81a5-f954-43f9-bf91-5df18eeb9aba

import Definitions.Def_CauchyRiemannIndex_Setting
import Definitions.Def_ConleyZehnder_Setting
import Mathlib.Analysis.Calculus.Deriv.Prod

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
# Block-diagonal sums of asymptotic coefficients
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem isAsymptoticTo_diamond_aux {m₁ m₂ : ℕ} (S₁ : ℝ × ℝ → Mat m₁) (S₂ : ℝ × ℝ → Mat m₂)
    (Ap Am : ℝ → Mat m₁) (Bp Bm : ℝ → Mat m₂) (h₁ : IsAsymptoticTo S₁ Ap Am)
    (h₂ : IsAsymptoticTo S₂ Bp Bm) :
    IsAsymptoticTo (fun x => ConleyZehnder.diamond (S₁ x) (S₂ x))
      (fun t => ConleyZehnder.diamond (Ap t) (Bp t))
      (fun t => ConleyZehnder.diamond (Am t) (Bm t)) := by
  obtain ⟨hc₁, hp₁, ha₁⟩ := h₁
  obtain ⟨hc₂, hp₂, ha₂⟩ := h₂
  refine ⟨CRIFD.continuous_diamond hc₁ hc₂, fun s t => by simp only [hp₁ s t, hp₂ s t],
    fun ε hε => ?_⟩
  obtain ⟨R₁, hR₁⟩ := ha₁ ε hε
  obtain ⟨R₂, hR₂⟩ := ha₂ ε hε
  refine ⟨max R₁ R₂, fun s t i j => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · exact CRIFD.abs_sub_diamond_le _ _ _ _ hε.le
      (fun a b => (hR₁ s t a b).1 ((le_max_left _ _).trans hs))
      (fun a b => (hR₂ s t a b).1 ((le_max_right _ _).trans hs)) i j
  · exact CRIFD.abs_sub_diamond_le _ _ _ _ hε.le
      (fun a b => (hR₁ s t a b).2 (hs.trans (neg_le_neg (le_max_left _ _))))
      (fun a b => (hR₂ s t a b).2 (hs.trans (neg_le_neg (le_max_right _ _)))) i j

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution {m₁ m₂ : ℕ} (S₁ : ℝ × ℝ → Mat m₁) (S₂ : ℝ × ℝ → Mat m₂)
    (Ap Am : ℝ → Mat m₁) (Bp Bm : ℝ → Mat m₂) (h₁ : IsAsymptoticTo S₁ Ap Am)
    (h₂ : IsAsymptoticTo S₂ Bp Bm) :
    IsAsymptoticTo (fun x => ConleyZehnder.diamond (S₁ x) (S₂ x))
      (fun t => ConleyZehnder.diamond (Ap t) (Bp t))
      (fun t => ConleyZehnder.diamond (Am t) (Bm t)) :=
  CauchyRiemannIndex.isAsymptoticTo_diamond_aux S₁ S₂ Ap Am Bp Bm h₁ h₂
