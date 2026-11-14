-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb53_original_expected_cash_monotone_eventual_upper_implies_every_horizon_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:04:37.736726+00:00
-- url     : https://prove2.me/submissions/c8a31718-3e05-4d3b-bb04-4e1a0f7948af

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- An asymptotic one-clock expected cash upper bound suffices for each
earlier strictly stopped horizon when actual cash is increasing a.e. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (w : ℝ)
    (hInt : ∀ n, Integrable (F n) P)
    (hMono : ∀ n m, n ≤ m → ∀ᵐ ω ∂P, F n ω ≤ F m ω)
    (hUpper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m in (atTop : Filter ℕ), (∫ ω, F m ω ∂P) ≤ w + ε) :
    ∀ n : ℕ, (∫ ω, F n ω ∂P) ≤ w := by
  intro n
  by_contra hn
  have hlt : w < (∫ ω, F n ω ∂P) := lt_of_not_ge hn
  let ε : ℝ := ((∫ ω, F n ω ∂P) - w) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 (hUpper ε hε)
  let m : ℕ := max n N
  have hnm : n ≤ m := le_max_left n N
  have hNm : N ≤ m := le_max_right n N
  have hmn : (∫ ω, F n ω ∂P) ≤ (∫ ω, F m ω ∂P) :=
    integral_mono_ae (hInt n) (hInt m) (hMono n m hnm)
  have hb : (∫ ω, F m ω ∂P) ≤ w + ε := hN m hNm
  dsimp [ε] at hb
  linarith
