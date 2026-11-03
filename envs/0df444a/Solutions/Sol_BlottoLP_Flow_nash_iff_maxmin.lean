-- Prove2me | solution 1 for BlottoLP.Flow.nash_iff_maxmin
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:14:08.858604+00:00
-- url     : https://prove2.me/submissions/ac1ad1e5-71ac-45f1-a3a0-a55126821fcc

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Theorems.Thm_MatousekLP_ZeroSum_minimax_theorem

namespace BlottoLP.Flow.NashAux

open Finset Matrix BlottoLP.Flow

theorem pay_eq {α β : Type*} [Fintype α] [Fintype β] (M : α → β → ℝ)
    (ea : α ≃ Fin (Fintype.card α)) (eb : β ≃ Fin (Fintype.card β))
    (σ : α → ℝ) (τ : β → ℝ) :
    MatousekLP.ZeroSum.payoff (fun i j => M (ea.symm i) (eb.symm j)) (σ ∘ ea.symm)
      (τ ∘ eb.symm) = expPay M σ τ := by
  unfold MatousekLP.ZeroSum.payoff expPay
  simp only [dotProduct, mulVec, Function.comp_apply, mul_sum]
  rw [← Equiv.sum_comp ea.symm.symm]
  refine sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp eb.symm.symm]
  refine sum_congr rfl fun b _ => ?_
  simp only [Equiv.symm_symm, Equiv.symm_apply_apply]
  ring

theorem mixed_iff {α : Type*} [Fintype α] (ea : α ≃ Fin (Fintype.card α)) (σ : α → ℝ) :
    σ ∘ ea.symm ∈ stdSimplex ℝ (Fin (Fintype.card α)) ↔ IsMixed σ := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => ?_, ?_⟩
    · have := h1 (ea a); simpa using this
    · rw [← h2]; exact (Equiv.sum_comp ea.symm σ).symm
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => h1 _, ?_⟩
    rw [← h2]; exact Equiv.sum_comp ea.symm σ

/-- Existence of a Nash equilibrium in a finite zero-sum game with nonempty strategy sets. -/
theorem nash_exists {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (M : α → β → ℝ) : ∃ σ τ, IsNashEq M σ τ := by
  let ea := Fintype.equivFin α
  let eb := Fintype.equivFin β
  let Mf : Matrix (Fin (Fintype.card α)) (Fin (Fintype.card β)) ℝ :=
    fun i j => M (ea.symm i) (eb.symm j)
  obtain ⟨⟨xt, hxt⟩, ⟨yt, hyt⟩, hnash, -⟩ :=
    MatousekLP.ZeroSum.minimax_theorem Fintype.card_pos Fintype.card_pos Mf
  obtain ⟨⟨hx, hxbr⟩, ⟨hy, hybr⟩⟩ := hnash xt yt hxt hyt
  have ex : (xt ∘ ea) ∘ ea.symm = xt := by funext i; simp
  have ey : (yt ∘ eb) ∘ eb.symm = yt := by funext i; simp
  refine ⟨xt ∘ ea, yt ∘ eb, ?_, ?_, ?_, ?_⟩
  · rw [← mixed_iff ea, ex]; exact hx
  · rw [← mixed_iff eb, ey]; exact hy
  · intro σ' hσ'
    rw [← pay_eq M ea eb, ← pay_eq M ea eb, ex, ey]
    exact hxbr _ ((mixed_iff ea σ').2 hσ')
  · intro τ' hτ'
    rw [← pay_eq M ea eb, ← pay_eq M ea eb, ex, ey]
    exact hybr _ ((mixed_iff eb τ').2 hτ')

theorem not_mixed_of_isEmpty {α : Type*} [Fintype α] [IsEmpty α] (σ : α → ℝ) : ¬ IsMixed σ := by
  rintro ⟨_, h⟩
  simp at h

end BlottoLP.Flow.NashAux

open BlottoLP.Flow BlottoLP.Flow.NashAux in
theorem solution {α β : Type*} [Fintype α] [Fintype β] (M : α → β → ℝ) :
    (∀ (σ : α → ℝ) (τ : β → ℝ), IsNashEq M σ τ ↔ IsMaxmin M σ ∧ IsMinmax M τ) ∧
    (∀ σ : α → ℝ, σ ∈ nashRow M ↔ IsMaxmin M σ) := by
  have part1 : ∀ (σ : α → ℝ) (τ : β → ℝ), IsNashEq M σ τ ↔ IsMaxmin M σ ∧ IsMinmax M τ := by
    intro σ τ
    constructor
    · rintro ⟨hσ, hτ, h1, h2⟩
      exact ⟨⟨hσ, expPay M σ τ, h2, fun σ' hσ' => ⟨τ, hτ, h1 σ' hσ'⟩⟩,
        ⟨hτ, expPay M σ τ, h1, fun τ' hτ' => ⟨σ, hσ, h2 τ' hτ'⟩⟩⟩
    · rintro ⟨⟨hσ, v, hv1, hv2⟩, ⟨hτ, w, hw1, hw2⟩⟩
      -- strategy sets are nonempty, so a Nash equilibrium exists
      have : Nonempty α := by
        by_contra h; rw [not_nonempty_iff] at h; exact not_mixed_of_isEmpty σ hσ
      have : Nonempty β := by
        by_contra h; rw [not_nonempty_iff] at h; exact not_mixed_of_isEmpty τ hτ
      obtain ⟨σs, τs, hs⟩ := nash_exists M
      obtain ⟨hσs, hτs, hs1, hs2⟩ := hs
      obtain ⟨τ', hτ', hle1⟩ := hv2 σs hσs
      obtain ⟨σ', hσ', hle2⟩ := hw2 τs hτs
      have a1 := hs2 τ' hτ'
      have a2 := hs1 σ' hσ'
      have b1 := hv1 τ hτ
      have b2 := hw1 σ hσ
      refine ⟨hσ, hτ, fun σ'' hσ'' => ?_, fun τ'' hτ'' => ?_⟩
      · have := hw1 σ'' hσ''; linarith
      · have := hv1 τ'' hτ''; linarith
  refine ⟨part1, fun σ => ?_⟩
  constructor
  · rintro ⟨τ, h⟩
    exact ((part1 σ τ).1 h).1
  · intro hσ
    obtain ⟨hσm, v, _, hv2⟩ := id hσ
    have : Nonempty α := by
      by_contra h; rw [not_nonempty_iff] at h; exact not_mixed_of_isEmpty σ hσm
    have : Nonempty β := by
      obtain ⟨τ, hτ, _⟩ := hv2 σ hσm
      by_contra h; rw [not_nonempty_iff] at h; exact not_mixed_of_isEmpty τ hτ
    obtain ⟨σs, τs, hs⟩ := nash_exists M
    have hτs := ((part1 σs τs).1 hs).2
    exact ⟨τs, (part1 σ τs).2 ⟨hσ, hτs⟩⟩
