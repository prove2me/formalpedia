-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_ruin_grid_two_component_limit_assembles_ito
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:17:53.201883+00:00
-- url     : https://prove2.me/submissions/c02ba749-a516-4818-98df-bbacb1560fc2

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

/-- The original ruin-stopped finite-grid chain assembles the genuine Itô–Meyer
identity as soon as its separate source and dividend mesh limits are supplied. -/
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
    (hDividendLimit : ∀ᵐ ω ∂P,
      Tendsto (fun n => Dividend n ω + Cash ω) atTop (𝓝 (H ω))) :
    ∀ᵐ ω ∂P, Term ω + Cash ω = w x + M ω + G ω + H ω := by
  filter_upwards [hSourceLimit, hDividendLimit] with ω hsl hdl
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
  have hlimit :
      Tendsto
        (fun n => w x + Source n ω + (Dividend n ω + Cash ω))
        atTop (𝓝 (w x + (M ω + G ω) + H ω)) :=
    (tendsto_const_nhds.add hsl).add hdl
  have hconstant :
      Tendsto (fun _ : ℕ => Term ω + Cash ω)
        atTop (𝓝 (w x + (M ω + G ω) + H ω)) :=
    hlimit.congr' (by
      filter_upwards [hgrid] with n hn
      exact hn.symm)
  have heq : Term ω + Cash ω = w x + (M ω + G ω) + H ω :=
    tendsto_nhds_unique tendsto_const_nhds hconstant
  linarith only [heq]
