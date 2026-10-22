-- Prove2me | solution 1 for ChoiceRM.Policy.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:58:33.672507+00:00
-- url     : https://prove2.me/submissions/02f15d4e-7be5-4490-9426-8e03a62dd4c2

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_Policy_Dominance
import Definitions.Def_ChoiceRM_Policy_Value
set_option autoImplicit false
open RevenueManagement ChoiceRM.Policy

theorem solution {n : ℕ} (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (P : Finset (Fin n) → Fin n → ℝ) (hP : IsChoiceModel P)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) (t x : ℕ) (ht : 1 ≤ t) (hx : 1 ≤ x) :
    ((0 < lam → 0 < deltaV lam P r (t - 1) x →
      ∀ T, IsDominated P r T → ¬ IsOptimalOffer lam P r t x T) ∧
    (deltaV lam P r (t - 1) x = 0 →
      ∃ T, IsNondominated P r T ∧ IsOptimalOffer lam P r t x T)) := by
  constructor
  · intro hl hΔ T hdom hopt
    obtain ⟨α, hα0, hα1, hcase⟩ := hdom
    set Δ := deltaV lam P r (t - 1) x with hΔdef
    have hg : ∀ S, expRevenue P r S - purchaseProb P S * Δ ≤
        expRevenue P r T - purchaseProb P T * Δ := by
      intro S
      have := hopt S
      unfold stageObj at this
      exact le_of_mul_le_mul_left this hl
    have hsum : ∑ S, α S * (expRevenue P r S - purchaseProb P S * Δ) ≤
        expRevenue P r T - purchaseProb P T * Δ := by
      calc ∑ S, α S * (expRevenue P r S - purchaseProb P S * Δ)
          ≤ ∑ S, α S * (expRevenue P r T - purchaseProb P T * Δ) :=
            Finset.sum_le_sum (fun S _ => mul_le_mul_of_nonneg_left (hg S) (hα0 S))
        _ = expRevenue P r T - purchaseProb P T * Δ := by rw [← Finset.sum_mul, hα1, one_mul]
    have hexp : ∑ S, α S * (expRevenue P r S - purchaseProb P S * Δ) =
        ∑ S, α S * expRevenue P r S - Δ * ∑ S, α S * purchaseProb P S := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun S _ => by ring)
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · nlinarith
    · nlinarith
  · intro hΔ
    obtain ⟨T0, -, hT0⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin n)))
      (fun S => expRevenue P r S) Finset.univ_nonempty
    obtain ⟨T, hTC, hTmin⟩ := Finset.exists_min_image
      (Finset.univ.filter (fun S => expRevenue P r S = expRevenue P r T0))
      (fun S => purchaseProb P S) ⟨T0, by simp⟩
    have hTR : expRevenue P r T = expRevenue P r T0 := (Finset.mem_filter.1 hTC).2
    have hmax : ∀ S, expRevenue P r S ≤ expRevenue P r T := fun S => by
      rw [hTR]; exact hT0 S (Finset.mem_univ _)
    refine ⟨T, ?_, ?_⟩
    · rintro ⟨α, hα0, hα1, hcase⟩
      have hle : ∑ S, α S * expRevenue P r S ≤ expRevenue P r T := by
        calc ∑ S, α S * expRevenue P r S ≤ ∑ S, α S * expRevenue P r T :=
              Finset.sum_le_sum (fun S _ => mul_le_mul_of_nonneg_left (hmax S) (hα0 S))
          _ = expRevenue P r T := by rw [← Finset.sum_mul, hα1, one_mul]
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith
      · have hQ : ∑ S, α S * purchaseProb P S < ∑ S, α S * purchaseProb P T := by
          rw [← Finset.sum_mul, hα1, one_mul]; exact h1
        obtain ⟨S, -, hS⟩ := Finset.exists_lt_of_sum_lt hQ
        have hαS : 0 < α S := by
          rcases (hα0 S).lt_or_eq with h | h
          · exact h
          · rw [← h] at hS; simp at hS
        have hQS : purchaseProb P S < purchaseProb P T := lt_of_mul_lt_mul_left hS (hα0 S)
        -- equality of revenues on the support
        have hsumeq : ∑ S, α S * (expRevenue P r T - expRevenue P r S) = 0 := by
          have : ∑ S, α S * (expRevenue P r T - expRevenue P r S) =
              expRevenue P r T - ∑ S, α S * expRevenue P r S := by
            simp only [mul_sub, Finset.sum_sub_distrib]
            rw [← Finset.sum_mul, hα1, one_mul]
          rw [this]; linarith
        have hnn : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
            0 ≤ α S * (expRevenue P r T - expRevenue P r S) :=
          fun S _ => mul_nonneg (hα0 S) (sub_nonneg.2 (hmax S))
        have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsumeq S (Finset.mem_univ _)
        have hRS : expRevenue P r S = expRevenue P r T := by
          rcases mul_eq_zero.1 hz with h | h
          · exact absurd h hαS.ne'
          · linarith
        have hmem : S ∈ Finset.univ.filter (fun S => expRevenue P r S = expRevenue P r T0) := by
          simp [hRS, hTR]
        have := hTmin S hmem
        linarith
    · intro S'
      unfold stageObj
      rw [hΔ]
      simp only [mul_zero, sub_zero]
      exact mul_le_mul_of_nonneg_left (hmax S') hlam0
