-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_true_cash_injective_atomic_subseries_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:41:32.505822+00:00
-- url     : https://prove2.me/submissions/1b3ef9bb-953c-4d29-8c88-08f39afeb7d9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_true_atom_discounted_cash_summable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The actual stopped original Stieltjes atomic cash sum is summable
on every injectively enumerated selection of the true countable carrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ A : Set ℝ, A.Countable ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      ∀ (g : ι → A), Function.Injective g →
        Summable (fun i : ι =>
          (μ {(g i : ℝ)} *
            (if (g i : ℝ) ∈ paymentTimes (ruinTime X x D ω)
              then ENNReal.ofReal (Real.exp (-(q * (g i : ℝ))))
              else 0)).toReal) := by
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  change ∃ A : Set ℝ, A.Countable ∧
    (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
    ∀ (g : ι → A), Function.Injective g →
      Summable (fun i : ι =>
        (μ {(g i : ℝ)} *
          (if (g i : ℝ) ∈ paymentTimes (ruinTime X x D ω)
            then ENNReal.ofReal (Real.exp (-(q * (g i : ℝ))))
            else 0)).toReal)
  obtain ⟨A, hCount, hSupport, hSummable⟩ :=
    avram_p4_d_dividend_original_stopped_true_atom_discounted_cash_summable
      X x q hq D hD ω T
  refine ⟨A, hCount, hSupport, ?_⟩
  intro g hg
  exact hSummable.comp_injective hg