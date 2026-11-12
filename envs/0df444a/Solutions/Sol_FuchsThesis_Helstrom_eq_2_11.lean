-- Prove2me | solution 1 for FuchsThesis.Helstrom.eq_2_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:20:00.531898+00:00
-- url     : https://prove2.me/submissions/e9c3ec6d-d418-4a81-8ac7-e21bcc56191b

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsProbDist

theorem solution {n : ℕ} (π0 π1 : ℝ) (hπ0 : 0 ≤ π0) (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1)
    (p0 p1 : Fin n → ℝ) (hp0 : FuchsVdGraaf.IsProbDist p0) (hp1 : FuchsVdGraaf.IsProbDist p1) :
    (∀ δ : Fin n → Fin 2,
        (∀ b, π1 * p1 b < π0 * p0 b → δ b = 0) →
        (∀ b, π0 * p0 b < π1 * p1 b → δ b = 1) →
        π0 * ∑ b, ((δ b : ℕ) : ℝ) * p0 b + π1 * ∑ b, (1 - ((δ b : ℕ) : ℝ)) * p1 b =
          ∑ b, min (π0 * p0 b) (π1 * p1 b)) ∧
      ∀ δ : Fin n → Fin 2,
        ¬ ((∀ b, π1 * p1 b < π0 * p0 b → δ b = 0) ∧ (∀ b, π0 * p0 b < π1 * p1 b → δ b = 1)) →
        ∑ b, min (π0 * p0 b) (π1 * p1 b) <
          π0 * ∑ b, ((δ b : ℕ) : ℝ) * p0 b + π1 * ∑ b, (1 - ((δ b : ℕ) : ℝ)) * p1 b := by
  have hsplit : ∀ δ : Fin n → Fin 2,
      π0 * ∑ b, ((δ b : ℕ) : ℝ) * p0 b + π1 * ∑ b, (1 - ((δ b : ℕ) : ℝ)) * p1 b =
        ∑ b, (π0 * (((δ b : ℕ) : ℝ) * p0 b) + π1 * ((1 - ((δ b : ℕ) : ℝ)) * p1 b)) := by
    intro δ
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hcases : ∀ (δ : Fin n → Fin 2) (b : Fin n),
      (((δ b : ℕ) : ℝ) = 0 ∧ δ b = 0) ∨ (((δ b : ℕ) : ℝ) = 1 ∧ δ b = 1) := by
    intro δ b
    have hlt := (δ b).isLt
    have h01 : (δ b : ℕ) = 0 ∨ (δ b : ℕ) = 1 := by omega
    rcases h01 with h | h
    · exact Or.inl ⟨by simp [h], Fin.ext (by simp [h])⟩
    · exact Or.inr ⟨by simp [h], Fin.ext (by simp [h])⟩
  constructor
  · intro δ h0 h1
    rw [hsplit]
    apply Finset.sum_congr rfl
    intro b _
    rcases hcases δ b with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · have hle : π1 * p1 b ≤ π0 * p0 b := by
        by_contra hlt
        push_neg at hlt
        have h' := h1 b hlt
        rw [hd] at h'
        exact absurd h' (by decide)
      rw [hc, min_eq_right hle]
      ring
    · have hle : π0 * p0 b ≤ π1 * p1 b := by
        by_contra hlt
        push_neg at hlt
        have h' := h0 b hlt
        rw [hd] at h'
        exact absurd h' (by decide)
      rw [hc, min_eq_left hle]
      ring
  · intro δ hnot
    rw [hsplit]
    have hle : ∀ b ∈ (Finset.univ : Finset (Fin n)), min (π0 * p0 b) (π1 * p1 b) ≤
        π0 * (((δ b : ℕ) : ℝ) * p0 b) + π1 * ((1 - ((δ b : ℕ) : ℝ)) * p1 b) := by
      intro b _
      rcases hcases δ b with ⟨hc, _⟩ | ⟨hc, _⟩
      · rw [hc]
        have := min_le_right (π0 * p0 b) (π1 * p1 b)
        linarith
      · rw [hc]
        have := min_le_left (π0 * p0 b) (π1 * p1 b)
        linarith
    have hex : ∃ b ∈ (Finset.univ : Finset (Fin n)), min (π0 * p0 b) (π1 * p1 b) <
        π0 * (((δ b : ℕ) : ℝ) * p0 b) + π1 * ((1 - ((δ b : ℕ) : ℝ)) * p1 b) := by
      by_contra hall
      push_neg at hall
      apply hnot
      constructor
      · intro b hlt
        rcases hcases δ b with ⟨_, hd⟩ | ⟨hc, _⟩
        · exact hd
        · exfalso
          have h' := hall b (Finset.mem_univ b)
          rw [hc, min_eq_right hlt.le] at h'
          linarith
      · intro b hlt
        rcases hcases δ b with ⟨hc, _⟩ | ⟨_, hd⟩
        · exfalso
          have h' := hall b (Finset.mem_univ b)
          rw [hc, min_eq_left hlt.le] at h'
          linarith
        · exact hd
    exact Finset.sum_lt_sum hle hex
