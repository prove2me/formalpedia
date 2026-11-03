-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_source_original_finite_mesh_ito_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:41:20.269207+00:00
-- url     : https://prove2.me/submissions/9ad187c0-7925-4dad-85f9-fec6e8307a89

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (clock : ℕ → ℝ≥0) (ω : Ω)
    (V : ℕ → ℝ)
    (hV : ∀ k, V k =
      Real.exp (-(q * (clock k : ℝ))) *
        w (x + X.X (clock k) ω - rightLimit D (clock k) ω))
    (CashZero : ℝ) (CashInc MInc GInc HInc : ℕ → ℝ)
    (hinit : V 0 + CashZero ≤ w x)
    (hcell : ∀ k, V (k + 1) + CashInc k ≤
      V k + MInc k + GInc k + HInc k)
    (N : ℕ) :
    Real.exp (-(q * (clock N : ℝ))) *
        w (x + X.X (clock N) ω - rightLimit D (clock N) ω) +
      CashZero + (∑ k ∈ Finset.range N, CashInc k) ≤
      w x + (∑ k ∈ Finset.range N, MInc k) +
        (∑ k ∈ Finset.range N, GInc k) +
        (∑ k ∈ Finset.range N, HInc k) := by
  rw [← hV N]
  induction N with
  | zero =>
      simpa using hinit
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      have hc := hcell N
      linarith
