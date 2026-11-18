-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva37_monotone_nonintegrable_signed_B_error_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:41:06.342328+00:00
-- url     : https://prove2.me/submissions/20697427-413e-45ec-851e-d54bca20eb48

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_two_scale_integrable_cash_expected_budget_without_B_L1
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F M B E : ℕ → Ω → ℝ) (a : ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hMono : ∀ n m, n ≤ m → (∫ ω, F n ω ∂P) ≤ (∫ ω, F m ω ∂P))
    (hMI : ∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0)
    (hEI : ∀ n, Integrable (fun ω => max (E n ω) 0) P)
    (hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ a + M n ω + B n ω + max (E n ω) 0)
    (hErr : Tendsto (fun n => ∫ ω, max (E n ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ n, (∫ ω, F n ω ∂P) ≤ a := by
  have hRow (n : ℕ) :
      (∫ ω, F n ω ∂P) ≤
      a + (∫ ω, max (E n ω) 0 ∂P) := by
    have hr :=
      avram_bvb_two_scale_integrable_cash_expected_budget_without_B_L1
        a (F n) (M n) (B n) (E n) (fun _ => 0)
        (hFI n) (hMI n).1 (hMI n).2 (hEI n)
        (by simpa using (integrable_const (0 : ℝ))) (hB n)
        (by simpa using hBudget n)
    simpa using hr
  intro n
  by_contra hn
  have hgt : a < (∫ ω, F n ω ∂P) := lt_of_not_ge hn
  have hε : 0 < ((∫ ω, F n ω ∂P) - a) / 2 := by linarith
  have hEvent : ∀ᶠ m : ℕ in atTop,
      (∫ ω, max (E m ω) 0 ∂P) < ((∫ ω, F n ω ∂P) - a) / 2 :=
    hErr.eventually (Iio_mem_nhds hε)
  obtain ⟨m, hnm, hm⟩ :=
    ((Filter.eventually_ge_atTop n).and hEvent).exists
  have hmn := (hMono n m hnm).trans (hRow m)
  linarith
