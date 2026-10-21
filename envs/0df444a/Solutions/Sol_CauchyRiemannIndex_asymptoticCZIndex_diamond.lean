-- Prove2me | solution 1 for CauchyRiemannIndex.asymptoticCZIndex_diamond
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-20T15:47:44.906478+00:00
-- url     : https://prove2.me/submissions/0ce7398e-9535-48dc-bbc2-63515760204c

import Definitions.Def_CauchyRiemannIndex_Setting
import Definitions.Def_ConleyZehnder_Setting
import Mathlib.Analysis.Calculus.Deriv.Prod
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic
import Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_eq_czIndex
import Theorems.Thm_ConleyZehnder_czIndex_product

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
# The Conley–Zehnder index of a block-diagonal asymptotic operator
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

lemma crif_fund_diamond {m₁ m₂ : ℕ} {A : ℝ → Mat m₁} {B : ℝ → Mat m₂} {ΨA : ℝ → Mat m₁}
    {ΨB : ℝ → Mat m₂} (hA : IsFundamentalSolution A ΨA) (hB : IsFundamentalSolution B ΨB) :
    IsFundamentalSolution (fun t => ConleyZehnder.diamond (A t) (B t))
      (fun t => ConleyZehnder.diamond (ΨA t) (ΨB t)) := by
  refine ⟨by simp only [hA.1, hB.1, CRIFD.diamond_one], fun t => ?_⟩
  have h := CRIFD.hasDerivAt_diamond (hA.2 t) (hB.2 t)
  convert h using 1
  rw [CRIFD.J_eq_diamond, ← CRIFD.diamond_mul, ← CRIFD.diamond_mul]

lemma crif_continuous_of_fund {m : ℕ} {S Ψ : ℝ → Mat m} (h : IsFundamentalSolution S Ψ) :
    Continuous Ψ :=
  continuous_pi fun i => continuous_pi fun j => continuous_iff_continuousAt.2 fun t =>
    ((CRIFD.hasDerivAt_mat_iff.1 (h.2 t)) i j).continuousAt

lemma crif_mem_SP {m : ℕ} {S : ℝ → Mat m} (hS : IsSymLoop S) (hn : IsNondegenerate S)
    {Ψ : ℝ → Mat m} (hΨ : IsFundamentalSolution S Ψ) :
    (⟨fun t : unitInterval => Ψ t, (crif_continuous_of_fund hΨ).comp continuous_subtype_val⟩ :
      C(unitInterval, Mat m)) ∈ ConleyZehnder.SP m := by
  refine ⟨fun t => fundamentalSolution_symplectic m S hS.2.2 Ψ hΨ t, ?_, ?_⟩
  · show Ψ ((0 : unitInterval) : ℝ) = 1
    rw [Set.Icc.coe_zero]; exact hΨ.1
  · show (1 - Ψ ((1 : unitInterval) : ℝ)).det ≠ 0
    rw [Set.Icc.coe_one]; exact hn Ψ hΨ

theorem asymptoticCZIndex_diamond_aux {m₁ m₂ : ℕ} (A : ℝ → Mat m₁) (B : ℝ → Mat m₂)
    (hA : IsSymLoop A) (hB : IsSymLoop B) (hnA : IsNondegenerate A) (hnB : IsNondegenerate B) :
    IsSymLoop (fun t => ConleyZehnder.diamond (A t) (B t)) ∧
      IsNondegenerate (fun t => ConleyZehnder.diamond (A t) (B t)) ∧
      asymptoticCZIndex (fun t => ConleyZehnder.diamond (A t) (B t)) =
        asymptoticCZIndex A + asymptoticCZIndex B := by
  obtain ⟨ΨA, hΨA, -⟩ := fundamentalSolution_existsUnique m₁ A hA.1
  obtain ⟨ΨB, hΨB, -⟩ := fundamentalSolution_existsUnique m₂ B hB.1
  have hD : IsSymLoop (fun t => ConleyZehnder.diamond (A t) (B t)) := by
    refine ⟨CRIFD.continuous_diamond hA.1 hB.1, fun t => by simp only [hA.2.1 t, hB.2.1 t],
      fun t => ?_⟩
    show (ConleyZehnder.diamond (A t) (B t))ᵀ = _
    rw [CRIFD.diamond_transpose, (hA.2.2 t).eq, (hB.2.2 t).eq]
  have hF := crif_fund_diamond hΨA hΨB
  obtain ⟨ΨD, -, huniq⟩ := fundamentalSolution_existsUnique (m₁ + m₂) _ hD.1
  have hnd : IsNondegenerate (fun t => ConleyZehnder.diamond (A t) (B t)) := by
    intro Ψ hΨ
    rw [(huniq Ψ hΨ).trans (huniq _ hF).symm]
    show (1 - ConleyZehnder.diamond (ΨA 1) (ΨB 1)).det ≠ 0
    rw [← CRIFD.diamond_one (m₁ := m₁) (m₂ := m₂), ← CRIFD.diamond_sub, CRIFD.det_diamond]
    exact mul_ne_zero (hnA ΨA hΨA) (hnB ΨB hΨB)
  refine ⟨hD, hnd, ?_⟩
  set ψA : C(unitInterval, Mat m₁) :=
    ⟨fun t : unitInterval => ΨA t, (crif_continuous_of_fund hΨA).comp continuous_subtype_val⟩
  set ψB : C(unitInterval, Mat m₂) :=
    ⟨fun t : unitInterval => ΨB t, (crif_continuous_of_fund hΨB).comp continuous_subtype_val⟩
  set ψD : C(unitInterval, Mat (m₁ + m₂)) :=
    ⟨fun t : unitInterval => ConleyZehnder.diamond (ΨA t) (ΨB t),
      (crif_continuous_of_fund hF).comp continuous_subtype_val⟩
  have hP := ConleyZehnder.czIndex_product ψA (crif_mem_SP hA hnA hΨA) ψB
    (crif_mem_SP hB hnB hΨB) ψD (fun _ => rfl)
  rw [asymptoticCZIndex_eq_czIndex _ _ hD hnd _ hF ψD (fun _ => rfl),
    asymptoticCZIndex_eq_czIndex _ _ hA hnA _ hΨA ψA (fun _ => rfl),
    asymptoticCZIndex_eq_czIndex _ _ hB hnB _ hΨB ψB (fun _ => rfl)]
  exact hP

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution {m₁ m₂ : ℕ} (A : ℝ → Mat m₁) (B : ℝ → Mat m₂)
    (hA : IsSymLoop A) (hB : IsSymLoop B) (hnA : IsNondegenerate A) (hnB : IsNondegenerate B) :
    IsSymLoop (fun t => ConleyZehnder.diamond (A t) (B t)) ∧
      IsNondegenerate (fun t => ConleyZehnder.diamond (A t) (B t)) ∧
      asymptoticCZIndex (fun t => ConleyZehnder.diamond (A t) (B t)) =
        asymptoticCZIndex A + asymptoticCZIndex B :=
  CauchyRiemannIndex.asymptoticCZIndex_diamond_aux A B hA hB hnA hnB
