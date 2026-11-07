-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict10_two_scale_positive_excess_of_cell_and_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:30:54.824441+00:00
-- url     : https://prove2.me/submissions/271b1ab9-d5ea-4a23-b249-3e173bd70c73

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_two_positive_errors_exact_excess_without_B_L1
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Original two-scale zero-mean source estimates with separate compact
    C1 and ruin-contact errors imply the non-L1 exact excess certificate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (F B : ℕ → Ω → ℝ) (base : ℝ)
    (M ErrCell ErrContact : ℕ → ℕ → Ω → ℝ)
    (η : ℕ → ℝ)
    (hηpos : ∀ n, 0 < η n)
    (hηzero : Tendsto η atTop (nhds (0 : ℝ)))
    (hM : ∀ n k, Integrable (M n k) P ∧
      (∫ ω, M n k ω ∂P) = 0)
    (hCell : ∀ n k, Integrable
      (fun ω => max (ErrCell n k ω) 0) P)
    (hContact : ∀ n k, Integrable
      (fun ω => max (ErrContact n k ω) 0) P)
    (hExcessMeas : ∀ n k, AEStronglyMeasurable
      (fun ω => max (F n ω - (base + (M n k ω + B n ω))) 0) P)
    (hBudget : ∀ n k, ∀ᵐ ω ∂P,
      F n ω ≤ base + (M n k ω + B n ω) +
        max (ErrCell n k ω) 0 + max (ErrContact n k ω) 0)
    (hPick : ∀ n (ε : ℝ), 0 < ε →
      ∃ k : ℕ,
        (∫ ω, max (ErrCell n k ω) 0 ∂P) +
          (∫ ω, max (ErrContact n k ω) 0 ∂P) ≤ η n + ε) :
    ∃ (M' : ℕ → ℕ → Ω → ℝ) (η' : ℕ → ℝ),
      (∀ n, 0 < η' n) ∧
      Tendsto η' atTop (nhds (0 : ℝ)) ∧
      (∀ n k, Integrable (M' n k) P ∧
        (∫ ω, M' n k ω ∂P) = 0) ∧
      (∀ n k, Integrable (fun ω =>
        max (F n ω - (base + (M' n k ω + B n ω))) 0) P) ∧
      (∀ n (ε : ℝ), 0 < ε →
        ∃ k : ℕ,
          (∫ ω,
            max (F n ω - (base + (M' n k ω + B n ω))) 0 ∂P)
            ≤ η' n + ε) := by
  refine ⟨M, η, hηpos, hηzero, hM, ?_, ?_⟩
  · intro n k
    exact (AvramDividend.Classical.avram_bv_strict10_two_positive_errors_exact_excess_without_B_L1
      P (F n) (M n k) (B n) (ErrCell n k) (ErrContact n k) base
        (hCell n k) (hContact n k) (hExcessMeas n k)
        (hBudget n k)).1
  · intro n ε hε
    obtain ⟨k, hk⟩ := hPick n ε hε
    refine ⟨k, ?_⟩
    exact (AvramDividend.Classical.avram_bv_strict10_two_positive_errors_exact_excess_without_B_L1
      P (F n) (M n k) (B n) (ErrCell n k) (ErrContact n k) base
        (hCell n k) (hContact n k) (hExcessMeas n k)
        (hBudget n k)).2.trans hk
