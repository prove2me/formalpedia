-- Prove2me | solution 1 for CaiCandesShen.Convergence.sampling_reduction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:57:19.878099+00:00
-- url     : https://prove2.me/submissions/578d2f2b-a2a8-4f98-9c38-413245b00512

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Iterations

namespace CaiCandesShen.Convergence

theorem aux_ssr_adjA_add {n₁ n₂ m : ℕ} (A : Fin m → Mat n₁ n₂) (u v : Fin m → ℝ) :
    adjA A (u + v) = adjA A u + adjA A v := by
  unfold adjA
  simp [add_smul, Finset.sum_add_distrib]

theorem aux_ssr_adjA_smul {n₁ n₂ m : ℕ} (A : Fin m → Mat n₁ n₂) (c : ℝ) (u : Fin m → ℝ) :
    adjA A (c • u) = c • adjA A u := by
  unfold adjA
  simp [Finset.smul_sum, smul_smul]

theorem aux_ssr_adjA_zero {n₁ n₂ m : ℕ} (A : Fin m → Mat n₁ n₂) :
    adjA A 0 = 0 := by
  unfold adjA
  simp

theorem aux_ssr_applyA_sub {n₁ n₂ m : ℕ} (A : Fin m → Mat n₁ n₂) (M X : Mat n₁ n₂) :
    applyA A (M - X) = applyA A M - applyA A X := by
  funext i
  simp [applyA, frobInner, mul_sub, Finset.sum_sub_distrib]

theorem aux_ssr_frob_single {n₁ n₂ : ℕ} (a : Fin n₁) (b : Fin n₂) (X : Mat n₁ n₂) :
    frobInner (Matrix.single a b (1 : ℝ)) X = X a b := by
  unfold frobInner
  simp [Matrix.single_apply, ite_and]

theorem aux_ssr_part1 {n₁ n₂ m : ℕ} (ω : Fin m → Fin n₁ × Fin n₂)
    (hω : Function.Injective ω) (Ω : Finset (Fin n₁ × Fin n₂))
    (hΩ : Ω = Finset.univ.image ω) (X : Mat n₁ n₂) :
    adjA (samplingOp ω) (applyA (samplingOp ω) X) = projΩ Ω X := by
  ext a b
  have key : ∀ i : Fin m, (applyA (samplingOp ω) X i • samplingOp ω i) a b
      = if ω i = (a, b) then X a b else 0 := by
    intro i
    simp only [applyA, samplingOp, aux_ssr_frob_single, Matrix.smul_apply, Matrix.single_apply,
      smul_eq_mul]
    by_cases h : ω i = (a, b)
    · simp [h]
    · have : ¬ ((ω i).1 = a ∧ (ω i).2 = b) := by
        rintro ⟨h1, h2⟩
        exact h (Prod.ext h1 h2)
      simp [h, this]
  unfold adjA
  rw [Matrix.sum_apply]
  simp only [key]
  unfold projΩ
  subst hΩ
  by_cases hm : (a, b) ∈ Finset.univ.image ω
  · rw [if_pos hm]
    obtain ⟨i0, -, hi0⟩ := Finset.mem_image.mp hm
    rw [Finset.sum_eq_single i0]
    · simp [hi0]
    · intro j _ hj
      have : ω j ≠ (a, b) := by
        intro h
        exact hj (hω (h.trans hi0.symm))
      simp [this]
    · simp
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro j _
    have : ω j ≠ (a, b) := by
      intro h
      exact hm (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h⟩)
    simp [this]

end CaiCandesShen.Convergence

open CaiCandesShen.Convergence

theorem solution {n₁ n₂ m : ℕ} (ω : Fin m → Fin n₁ × Fin n₂)
    (hω : Function.Injective ω) (Ω : Finset (Fin n₁ × Fin n₂))
    (hΩ : Ω = Finset.univ.image ω) :
    (∀ X : Mat n₁ n₂, adjA (samplingOp ω) (applyA (samplingOp ω) X) = projΩ Ω X) ∧
    ∀ (τ : ℝ) (M : Mat n₁ n₂) (b : Fin m → ℝ) (δ : ℕ → ℝ) (X : ℕ → Mat n₁ n₂)
      (y : ℕ → Fin m → ℝ),
      applyA (samplingOp ω) M = b → IsUzawaSeq τ (samplingOp ω) b δ X y →
        IsSVTSeq τ Ω M δ X (fun k => adjA (samplingOp ω) (y k)) := by
  have h1 := aux_ssr_part1 ω hω Ω hΩ
  refine ⟨h1, ?_⟩
  intro τ M b δ X y hb hU
  obtain ⟨hy0, hk⟩ := hU
  refine ⟨?_, ?_⟩
  · simp only [hy0, aux_ssr_adjA_zero]
  · intro k
    obtain ⟨hs, hy⟩ := hk k
    refine ⟨hs, ?_⟩
    simp only
    rw [hy, aux_ssr_adjA_add, aux_ssr_adjA_smul, ← hb, ← aux_ssr_applyA_sub, h1]
