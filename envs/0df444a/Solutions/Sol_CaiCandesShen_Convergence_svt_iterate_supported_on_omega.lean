-- Prove2me | solution 1 for CaiCandesShen.Convergence.svt_iterate_supported_on_omega
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:41:20.406625+00:00
-- url     : https://prove2.me/submissions/4a97e1a4-5120-4568-a96b-cb1d7c3950a4

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Iterations

namespace CaiCandesShen.Convergence

theorem aux_svtsupp_step {n₁ n₂ : ℕ} (Ω : Finset (Fin n₁ × Fin n₂)) (A B : Mat n₁ n₂) (c : ℝ)
    (hA : projΩ Ω A = A) : projΩ Ω (A + c • projΩ Ω B) = A + c • projΩ Ω B := by
  funext i j
  have h := congrFun (congrFun hA i) j
  simp only [projΩ] at h ⊢
  by_cases hij : (i, j) ∈ Ω
  · simp [hij]
  · simp only [hij, if_false] at h
    simp [projΩ, hij, ← h]

end CaiCandesShen.Convergence

open CaiCandesShen.Convergence

theorem solution {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (Ω : Finset (Fin n₁ × Fin n₂)) (M : Mat n₁ n₂) (δ : ℕ → ℝ) (hδ : ∀ k, 1 ≤ k → 0 < δ k)
    (X Y : ℕ → Mat n₁ n₂) (hXY : IsSVTSeq τ Ω M δ X Y) :
    ∀ k : ℕ, projΩ Ω (Y k) = Y k := by
  obtain ⟨h0, hs⟩ := hXY
  intro k
  induction k with
  | zero =>
    rw [h0]
    funext i j
    simp [projΩ]
  | succ k ih =>
    rw [(hs k).2]
    exact aux_svtsupp_step Ω (Y k) (M - X (k + 1)) (δ (k + 1)) ih
