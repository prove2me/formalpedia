-- Prove2me | solution 1 for AvramDividend.Classical.chat04_standing_cantor_grid_survival_scale_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:10:11.221769+00:00
-- url     : https://prove2.me/submissions/14083d51-12f8-4e06-b241-3c3249913ffa

import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_chat04_countable_grid_strict_survival_event_eq
import Theorems.Thm_AvramDividend_Classical_chat04_countable_grid_survival_prefix_limit
import Theorems.Thm_AvramDividend_Classical_chat04_standing_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
For every fixed horizon, the expected positive q-scale payoff killed by
continuous-time strict exit is the decreasing infimum of expectations killed
on finite prefixes of an EXPLICIT Cantor-paired reciprocal rational grid.
Integrability follows from original Standing, without an extra assumption.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x lower upper : ℝ) (T : ℝ≥0) :
    (∫⁻ ω,
      ({ω | ∀ t : ℝ≥0,
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator
          (fun ω => ENNReal.ofReal (W (x + X.X T ω))) ω ∂P) =
      ⨅ n : ℕ, ∫⁻ ω,
        ({ω | ∀ j ≤ n,
          ¬ (X.X (((Nat.unpair j).2 : ℝ≥0) *
            ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹)) ω < lower ∨
              upper < X.X (((Nat.unpair j).2 : ℝ≥0) *
            ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹)) ω)}).indicator
          (fun ω => ENNReal.ofReal (W (x + X.X T ω))) ω ∂P := by
  let τ : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹)
  let B : ℕ → Set Ω := fun j =>
    {ω | ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)}
  let g : Ω → ℝ≥0∞ :=
    fun ω => ENNReal.ofReal (W (x + X.X T ω))
  have hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹ := by
    intro n hn k
    simpa only [τ] using
      (AvramDividend.Classical.chat04_nat_pairing_rational_grid_coverage
        n k hn)
  have hB : ∀ j, MeasurableSet (B j) := by
    intro j
    have hXt : Measurable (X.X (τ j)) :=
      (X.adapted (τ j)).mono (𝓕.le (τ j)) le_rfl
    have hLow : MeasurableSet {ω : Ω | X.X (τ j) ω < lower} :=
      measurableSet_lt hXt measurable_const
    have hUp : MeasurableSet {ω : Ω | upper < X.X (τ j) ω} :=
      measurableSet_lt measurable_const hXt
    change MeasurableSet
      ({ω : Ω | X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω}ᶜ)
    exact (hLow.union hUp).compl
  have hWm : Measurable W :=
    AvramDividend.Classical.chat03_scale_function_borel_measurable
      X q W hW
  have hXt : Measurable (X.X T) :=
    (X.adapted T).mono (𝓕.le T) le_rfl
  have hFm : Measurable (fun ω : Ω => W (x + X.X T ω)) :=
    hWm.comp (measurable_const.add hXt)
  have hg : Measurable g :=
    ENNReal.measurable_ofReal.comp hFm
  have hNonneg : 0 ≤ᵐ[P] (fun ω => W (x + X.X T ω)) := by
    filter_upwards [] with ω
    by_cases hn : x + X.X T ω < 0
    · rw [hW.1 _ hn]
      exact le_rfl
    · exact hW.2.1 _ (le_of_not_gt hn)
  have hInt : Integrable (fun ω => W (x + X.X T ω)) P :=
    AvramDividend.Classical.chat04_standing_scale_fixed_time_integrable
      X hX q hq W hW x T
  have hFin : (∫⁻ ω, g ω ∂P) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable
      hFm.aestronglyMeasurable hNonneg).mpr hInt
  have hEvents :
      {ω | ∀ t : ℝ≥0,
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)} =
      ⋂ j, B j := by
    simpa only [B] using
      (AvramDividend.Classical.chat04_countable_grid_strict_survival_event_eq
        X τ hCover lower upper)
  rw [hEvents]
  simpa only [B, g, τ, Set.mem_setOf_eq] using
    (AvramDividend.Classical.chat04_countable_grid_survival_prefix_limit
      B hB g hg hFin)
