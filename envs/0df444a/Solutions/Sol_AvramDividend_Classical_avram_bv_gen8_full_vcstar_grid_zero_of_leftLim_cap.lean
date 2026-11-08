-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_full_vcstar_grid_zero_of_leftLim_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:52:36.302902+00:00
-- url     : https://prove2.me/submissions/837ca5a7-4a98-4793-822c-b179a35f3121

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_cell_supported_strict_above_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The entire original stopped BV candidate generator grid vanishes if
the actual physical left-limit reserve is below the optimal barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hZcap : ∀ n i ω, (u n i : ℝ≥0∞) < ruinTime X x D ω →
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ≤
        (cstar W).toReal) :
    let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    ∀ n, (∀ ω, (∑ i ∈ Finset.range (n + 1), H n i ω) = 0) ∧
      Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) P := by
  let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
  change ∀ n, (∀ ω, (∑ i ∈ Finset.range (n + 1), H n i ω) = 0) ∧
      Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) P
  have hcell : ∀ n i ω, H n i ω = 0 := by
    intro n i ω
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    have hsource :=
      avram_bv_gen8_original_vcstar_cell_supported_strict_above_cap
        X hX hBV q hq W hW hc hcpos hgen x D u n i ω
    change H n i ω =
      (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            (cstar W).toReal < Z then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
       else 0) at hsource
    rw [hsource]
    have hn : ¬ ((u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          (cstar W).toReal < Z) := by
      rintro ⟨hs, hz⟩
      exact (not_lt_of_ge (hZcap n i ω hs)) hz
    simp only [if_neg hn]
  have hs : ∀ n ω, (∑ i ∈ Finset.range (n + 1), H n i ω) = 0 := by
    intro n ω
    apply Finset.sum_eq_zero
    intro i hi
    exact hcell n i ω
  intro n
  refine ⟨hs n, ?_⟩
  have heq : (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) =
      (fun _ : Ω => (0 : ℝ)) := by
    funext ω
    exact hs n ω
  rw [heq]
  exact integrable_zero Ω ℝ P
