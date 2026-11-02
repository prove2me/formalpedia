-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_ruin_grid_source_limit_dividend_upper_assembles_ito_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:27:27.754583+00:00
-- url     : https://prove2.me/submissions/5f763e1c-9bb7-4edf-9a64-15eae0012ae1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_actual_ruin_stopped_random_grid_four_event_endpoint

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original-source grid limits and eventual Stieltjes domination imply the
one-sided controlled Itô–Meyer bound without an exact dividend limit. -/
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
    (hSourceLimit : ∀ᵐ ω ∂P,
      Tendsto (fun n => Source n ω) atTop (𝓝 (M ω + G ω)))
    (hDividendBound : ∀ᵐ ω ∂P,
      ∀ᶠ n in atTop, Dividend n ω + Cash ω ≤ H ω) :
    ∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω := by
  filter_upwards [hSourceLimit, hDividendBound] with ω hs hb
  have hgrid : ∀ᶠ n in atTop,
      Term ω + Cash ω =
        w x + Source n ω + (Dividend n ω + Cash ω) := by
    filter_upwards [hcover ω] with n hcov
    have hg :=
      avram_wave6_06_actual_ruin_stopped_random_grid_four_event_endpoint
        X x q D hD w ω τ (hτruin ω)
        (u n) (hmono n) (hzero n) (k n) hcov
    rw [hTerm ω, hDividend n ω]
    dsimp only at hg ⊢
    linear_combination hg
  have hbound : ∀ᶠ n in atTop,
      Term ω + Cash ω ≤ w x + Source n ω + H ω := by
    filter_upwards [hgrid, hb] with n heq hle
    rw [heq]
    linarith only [hle]
  have hlim :
      Tendsto (fun n => w x + Source n ω + H ω)
        atTop (𝓝 (w x + (M ω + G ω) + H ω)) :=
    (tendsto_const_nhds.add hs).add tendsto_const_nhds
  have heq : Term ω + Cash ω ≤ w x + (M ω + G ω) + H ω :=
    ge_of_tendsto hlim hbound
  linarith only [heq]
