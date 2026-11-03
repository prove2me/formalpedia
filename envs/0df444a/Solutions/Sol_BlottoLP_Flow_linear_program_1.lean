-- Prove2me | solution 1 for BlottoLP.Flow.linear_program_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:02:09.051209+00:00
-- url     : https://prove2.me/submissions/c2a17809-b9f0-40d9-ba7f-536c66435e56

import Mathlib
import Definitions.Def_BlottoLP_Flow_Model
import Theorems.Thm_BlottoLP_Flow_corollary_4_4
import Theorems.Thm_BlottoLP_Flow_lemma_4_5
import Theorems.Thm_BlottoLP_Flow_best_response_dp

namespace BlottoLP.Flow.LP1Aux

open Finset BlottoLP.Flow

theorem expPay_pure {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (M : α → β → ℝ)
    (σ : α → ℝ) (b : β) : expPay M σ (pureMixed b) = ∑ a, σ a * M a b := by
  unfold expPay pureMixed
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hb'; simp [hb']
  · simp

theorem expPay_mix {α β : Type*} [Fintype α] [Fintype β] (M : α → β → ℝ)
    (σ : α → ℝ) (τ : β → ℝ) : expPay M σ τ = ∑ b, τ b * ∑ a, σ a * M a b := by
  unfold expPay
  rw [Finset.sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun a _ => ?_
  ring

theorem pureMixed_isMixed {β : Type*} [Fintype β] [DecidableEq β] (b : β) :
    IsMixed (pureMixed b) := by
  refine ⟨fun b' => ?_, ?_⟩
  · unfold pureMixed; split_ifs <;> norm_num
  · simp [pureMixed]

/-- Given one Nash equilibrium `(σ₀, τ₀)`, the row strategies occurring in a Nash equilibrium
are exactly the mixed strategies guaranteeing the value against every pure column strategy. -/
theorem nashRow_iff {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (M : α → β → ℝ)
    (σ₀ : α → ℝ) (τ₀ : β → ℝ) (h : IsNashEq M σ₀ τ₀) (σ : α → ℝ) :
    σ ∈ nashRow M ↔ IsMixed σ ∧ ∀ b, expPay M σ₀ τ₀ ≤ ∑ a, σ a * M a b := by
  constructor
  · rintro ⟨τ, hσ, hτ, h1, h2⟩
    refine ⟨hσ, fun b => ?_⟩
    rw [← expPay_pure]
    calc expPay M σ₀ τ₀ ≤ expPay M σ₀ τ := h.2.2.2 τ hτ
      _ ≤ expPay M σ τ := h1 σ₀ h.1
      _ ≤ expPay M σ (pureMixed b) := h2 _ (pureMixed_isMixed b)
  · rintro ⟨hσ, hb⟩
    have hall : ∀ τ', IsMixed τ' → expPay M σ₀ τ₀ ≤ expPay M σ τ' := by
      intro τ' hτ'
      rw [expPay_mix M σ τ']
      calc expPay M σ₀ τ₀ = ∑ b, τ' b * expPay M σ₀ τ₀ := by rw [← Finset.sum_mul, hτ'.2, one_mul]
        _ ≤ _ := Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hb b) (hτ'.1 b)
    exact ⟨τ₀, hσ, h.2.1, fun σ' hσ' => (h.2.2.1 σ' hσ').trans (hall τ₀ h.2.1),
      fun τ' hτ' => (h.2.2.1 σ hσ).trans (hall τ' hτ')⟩

/-- Player A's expected payoff against a pure strategy of B, through A's marginals and the
weights (4). -/
theorem pay_pure_eq (I : Instance) (σ : Pure I.K I.A → ℝ) (y : Pure I.K I.B) :
    ∑ x, σ x * payoff I x y = - ∑ k, weightB I (marginal σ) k (y.1 k) := by
  unfold payoff weightB marginal
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_neg_distrib]
  rw [← Finset.sum_fiberwise (s := univ) (g := fun x : Pure I.K I.A => x.1 k)]
  refine sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine sum_congr (by ext; simp) fun x hx => ?_
  simp only [mem_filter, mem_univ, true_and] at hx
  rw [hx]; ring

end BlottoLP.Flow.LP1Aux

open BlottoLP.Flow BlottoLP.Flow.LP1Aux Finset in
theorem solution (I : Instance) (σ₀ : Pure I.K I.A → ℝ) (τ₀ : Pure I.K I.B → ℝ)
    (h : IsNashEq (payoff I) σ₀ τ₀) (xhat : Fin I.K × Fin (I.A + 1) → ℝ) :
    xhat ∈ PA I ↔
      ∃ (F : Edge I.K I.A → ℝ) (D : Fin (I.K + 1) → Fin (I.B + 1) → ℝ),
        IsUnitFlow F ∧ flowMarginal F = xhat ∧ IsDPBound (weightB I xhat) D ∧
          D (Fin.last I.K) (Fin.last I.B) ≤ - expPayoff I σ₀ τ₀ := by
  classical
  have hv : expPayoff I σ₀ τ₀ = expPay (payoff I) σ₀ τ₀ := rfl
  -- Step 1: membership in 𝒫_A via marginals and pure best responses of B.
  have step1 : xhat ∈ PA I ↔ (∃ σ, IsMixed σ ∧ marginal σ = xhat) ∧
      ∀ y : Pure I.K I.B, ∑ k, weightB I xhat k (y.1 k) ≤ - expPayoff I σ₀ τ₀ := by
    constructor
    · rintro ⟨σ, hσR, rfl⟩
      obtain ⟨hσ, hb⟩ := (nashRow_iff (payoff I) σ₀ τ₀ h σ).1 hσR
      refine ⟨⟨σ, hσ, rfl⟩, fun y => ?_⟩
      have := hb y
      rw [pay_pure_eq] at this
      rw [hv]; linarith
    · rintro ⟨⟨σ, hσ, hm⟩, hy⟩
      refine ⟨σ, (nashRow_iff (payoff I) σ₀ τ₀ h σ).2 ⟨hσ, fun y => ?_⟩, hm⟩
      rw [pay_pure_eq, hm]
      have := hy y
      rw [hv] at this; linarith
  -- Step 2: marginals of mixed strategies are exactly the marginals (3) of unit flows.
  have step2 : (∃ σ, IsMixed σ ∧ marginal σ = xhat) ↔
      ∃ F : Edge I.K I.A → ℝ, IsUnitFlow F ∧ flowMarginal F = xhat := by
    constructor
    · rintro ⟨σ, hσ, hm⟩
      obtain ⟨h1, h2⟩ := corollary_4_4 I.K I.A σ hσ
      exact ⟨flowOf σ, h1, h2.trans hm⟩
    · rintro ⟨F, hF, hm⟩
      rcases Nat.eq_zero_or_pos I.K with hK | hK
      · refine ⟨σ₀, h.1, ?_⟩
        funext p
        exact absurd p.1.isLt (by omega)
      · obtain ⟨σ, hσ, hflow, -⟩ := lemma_4_5 I.K I.A hK F hF
        refine ⟨σ, hσ, ?_⟩
        rw [← (corollary_4_4 I.K I.A σ hσ).2, hflow, hm]
  rw [step1, step2, best_response_dp]
  constructor
  · rintro ⟨⟨F, hF, hm⟩, D, hD, hl⟩
    exact ⟨F, D, hF, hm, hD, hl⟩
  · rintro ⟨F, D, hF, hm, hD, hl⟩
    exact ⟨⟨F, hF, hm⟩, D, hD, hl⟩
