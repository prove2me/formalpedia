-- Prove2me | solution 1 for FullPathSCC.ln_monotone_certainty_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:16:25.072584+00:00
-- url     : https://prove2.me/submissions/0cf4bbd2-293b-4dd6-8875-2f086f38e8af

import Mathlib

theorem solution {S : Type*} [Fintype S] (κ β : ℝ) (hκ : 0 < κ)
    (hβ : 0 ≤ β) (q : S → ℝ) (hq : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) (v w : S → ℝ)
    (hvw : ∀ j, v j ≤ w j) :
    -(1 / κ) * Real.log (∑ j, q j * Real.exp (-κ * β * v j)) ≤
      -(1 / κ) * Real.log (∑ j, q j * Real.exp (-κ * β * w j)) := by
  have hex : ∃ j, 0 < q j := by
    by_contra hc
    push_neg at hc
    have : ∑ j, q j = 0 := Finset.sum_eq_zero (fun j _ => le_antisymm (hc j) (hq j))
    linarith
  obtain ⟨j0, hj0⟩ := hex
  have hpos : 0 < ∑ j, q j * Real.exp (-κ * β * w j) := by
    apply Finset.sum_pos' (fun j _ => mul_nonneg (hq j) (Real.exp_pos _).le)
    exact ⟨j0, Finset.mem_univ _, mul_pos hj0 (Real.exp_pos _)⟩
  have hle : ∑ j, q j * Real.exp (-κ * β * w j) ≤ ∑ j, q j * Real.exp (-κ * β * v j) := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (hq j)
    apply Real.exp_le_exp.mpr
    have hkb : 0 ≤ κ * β := mul_nonneg hκ.le hβ
    have := mul_le_mul_of_nonneg_left (hvw j) hkb
    nlinarith
  have hlog := Real.log_le_log hpos hle
  have hneg : -(1 / κ) ≤ 0 := by
    have : 0 < 1 / κ := by positivity
    linarith
  exact mul_le_mul_of_nonpos_left hlog hneg
