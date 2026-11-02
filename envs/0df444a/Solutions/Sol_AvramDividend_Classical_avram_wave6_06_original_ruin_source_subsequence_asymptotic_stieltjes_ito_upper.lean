-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_ruin_source_subsequence_asymptotic_stieltjes_ito_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T00:28:09.838994+00:00
-- url     : https://prove2.me/submissions/b285d2a3-2c5c-46a6-b8cb-80534014c48a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_ruin_source_grid_asymptotic_dividend_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (τ : Ω → ℝ≥0)
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hmono : ∀ n, Monotone (u n))
    (hzero : ∀ n, u n 0 = 0)
    (hcover : ∀ ω, ∀ᶠ n in atTop, τ ω ≤ u n (k n))
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (Term Cash M G H : Ω → ℝ)
    (Source Dividend : ℕ → Ω → ℝ)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω))
    (hSource : ∀ n ω, Source n ω =
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (τ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      ∑ i ∈ Finset.range (k n),
        ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i)))))
    (hDividend : ∀ n ω, Dividend n ω =
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (τ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      let pre : Prop := τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      (w (x - rightLimit D 0 ω) - w x) +
        (∑ i ∈ Finset.range (k n),
          ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
            E (v (i + 1)) * (w (Z i) - w (Y (v i))) +
            E (v (i + 1)) *
              (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
            E (v (i + 1)) *
              (w (Y (v (i + 1))) -
                w (riskProcess X x D (v (i + 1)) ω)))) +
        (if pre then 0 else E (τ ω) *
          (w (riskProcess X x D (τ ω) ω) - w (Y (τ ω)))) -
        Source n ω)
    (hSourceSubsequence : ∀ᵐ ω ∂P,
      Tendsto (fun n => Source (φ n) ω) atTop (𝓝 (M ω + G ω)))
    (hDividendApproxSubsequence : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, Dividend (φ n) ω + Cash ω ≤ H ω + ε) :
    ∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω := by
  have hcoverSub : ∀ ω, ∀ᶠ n in atTop,
      τ ω ≤ u (φ n) (k (φ n)) := by
    intro ω
    exact hφ.eventually (hcover ω)
  exact avram_wave6_06_original_ruin_source_grid_asymptotic_dividend_upper
    X x q D hD w τ hτruin
    (fun n i => u (φ n) i) (fun n => k (φ n))
    (fun n => hmono (φ n)) (fun n => hzero (φ n)) hcoverSub
    Term Cash M G H (fun n => Source (φ n)) (fun n => Dividend (φ n))
    hTerm (fun n ω => hSource (φ n) ω)
    (fun n ω => hDividend (φ n) ω)
    hSourceSubsequence hDividendApproxSubsequence
