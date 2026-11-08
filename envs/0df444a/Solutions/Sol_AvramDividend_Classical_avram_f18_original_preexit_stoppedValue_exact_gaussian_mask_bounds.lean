-- Prove2me | solution 1 for AvramDividend.Classical.avram_f18_original_preexit_stoppedValue_exact_gaussian_mask_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:22:25.911201+00:00
-- url     : https://prove2.me/submissions/c353c75a-aa9a-46d7-881d-065571bcd051

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f17_original_preexit_source_ruin_indicator_gaussian_C2_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U)
    (τ : Ω → ℝ≥0) (Tmax : ℝ≥0)
    (hinterior : ∀ ω, ∃ T : ℝ≥0,
      0 < τ ω ∧ τ ω < T ∧
      (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤)) :
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ ω : Ω,
        |stoppedValue (fun t ω =>
          if t ≤ Tmax then
            (Real.exp (-(q * (t : ℝ))) *
              deriv w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
          else 0) (fun ω => (τ ω : WithTop ℝ≥0)) ω| ≤ KG ∧
        |stoppedValue (fun t ω =>
          if t ≤ Tmax then
            (Real.exp (-(q * (t : ℝ))) *
              (let y := Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
               if 0 < y ∧ ENNReal.ofReal y < C
               then iteratedDeriv 2 w y else 0)) *
            (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
          else 0) (fun ω => (τ ω : WithTop ℝ≥0)) ω| ≤ KH := by
  obtain ⟨KG, KH, hKG, hKH, hbound⟩ :=
    AvramDividend.Classical.avram_f17_original_preexit_source_ruin_indicator_gaussian_C2_bound
      X hBV hν q hq C w hw x D hD r lower upper hlower hcap hgrid
  refine ⟨KG, KH, hKG, hKH, ?_⟩
  intro ω
  rcases hinterior ω with ⟨T, hτpos, hτlt, hT⟩
  have hb := hbound ω T hT (τ ω) hτpos hτlt
  have hstopped (f : ℝ≥0 → Ω → ℝ) :
      MeasureTheory.stoppedValue f (fun ω => (τ ω : WithTop ℝ≥0)) ω =
        f (τ ω) ω := rfl
  constructor
  · rw [hstopped]
    by_cases hmax : τ ω ≤ Tmax
    · simpa only [if_pos hmax] using hb.1
    · simp only [if_neg hmax, abs_zero]
      exact hKG
  · rw [hstopped]
    by_cases hmax : τ ω ≤ Tmax
    · simpa only [if_pos hmax] using hb.2
    · simp only [if_neg hmax, abs_zero]
      exact hKH
