-- Prove2me | solution 1 for CaiCandesShen.Convergence.lagrangian_argmin_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:34:05.765521+00:00
-- url     : https://prove2.me/submissions/0c39af52-6d9e-4b8f-8aa0-344bb13db485

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic

namespace CaiCandesShen.Convergence

theorem aux_lae_inner_nonneg {n₁ n₂ : ℕ} (X : Mat n₁ n₂) : 0 ≤ frobInner X X := by
  unfold frobInner
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

theorem aux_lae_normsq {n₁ n₂ : ℕ} (X : Mat n₁ n₂) : frobNorm X ^ 2 = frobInner X X := by
  unfold frobNorm
  exact Real.sq_sqrt (aux_lae_inner_nonneg X)

theorem aux_lae_key {n₁ n₂ : ℕ} (Ω : Finset (Fin n₁ × Fin n₂)) (M Y X : Mat n₁ n₂) :
    frobInner Y (projΩ Ω (M - X)) + 1 / 2 * frobInner X X =
      1 / 2 * frobInner (X - projΩ Ω Y) (X - projΩ Ω Y) +
        (frobInner Y (projΩ Ω M) - 1 / 2 * frobInner (projΩ Ω Y) (projΩ Ω Y)) := by
  unfold frobInner
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [projΩ, Matrix.sub_apply]
  split_ifs <;> ring

theorem aux_lae_obj {n₁ n₂ : ℕ} (τ : ℝ) (Ω : Finset (Fin n₁ × Fin n₂)) (M Y X : Mat n₁ n₂) :
    fτ τ X + frobInner Y (projΩ Ω (M - X)) =
      (τ * nuclearNorm X + 1 / 2 * frobNorm (X - projΩ Ω Y) ^ 2) +
        (frobInner Y (projΩ Ω M) - 1 / 2 * frobInner (projΩ Ω Y) (projΩ Ω Y)) := by
  unfold fτ
  rw [aux_lae_normsq, aux_lae_normsq]
  have := aux_lae_key Ω M Y X
  linarith

end CaiCandesShen.Convergence

open CaiCandesShen.Convergence

theorem solution {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (Ω : Finset (Fin n₁ × Fin n₂)) (M Y : Mat n₁ n₂) :
    {X : Mat n₁ n₂ | ∀ X' : Mat n₁ n₂,
        fτ τ X + frobInner Y (projΩ Ω (M - X)) ≤ fτ τ X' + frobInner Y (projΩ Ω (M - X'))} =
      {X : Mat n₁ n₂ | ∀ X' : Mat n₁ n₂,
        τ * nuclearNorm X + 1 / 2 * frobNorm (X - projΩ Ω Y) ^ 2 ≤
          τ * nuclearNorm X' + 1 / 2 * frobNorm (X' - projΩ Ω Y) ^ 2} := by
  ext X
  simp only [Set.mem_setOf_eq, aux_lae_obj τ Ω M Y]
  exact forall_congr' fun X' => add_le_add_iff_right _
