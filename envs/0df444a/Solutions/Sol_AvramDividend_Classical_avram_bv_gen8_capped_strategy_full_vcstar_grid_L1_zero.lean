-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_capped_strategy_full_vcstar_grid_L1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:58:56.070778+00:00
-- url     : https://prove2.me/submissions/0cf71dfd-2299-41bf-b42e-5407b5fb9e6c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_full_vcstar_grid_zero_of_leftLim_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original cstar-capped admissible dividend strategy has a vanishing
full discounted generator grid, including every positive stopped cell. -/
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
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ cstar W)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (cstar W) D)
    (u : ℕ → ℕ → ℝ≥0) :
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
  have hZcap : ∀ n i ω, (u n i : ℝ≥0∞) < ruinTime X x D ω →
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ≤
        (cstar W).toReal := by
    intro n i ω hstop
    have hb := avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
      X x (cstar W) hxc D hD ω (u n i) (Or.inr hstop)
    exact (ENNReal.ofReal_le_iff_le_toReal (ne_of_lt hc)).mp hb.2
  exact avram_bv_gen8_full_vcstar_grid_zero_of_leftLim_cap
    X hX hBV q hq W hW hc hcpos hgen x D u hZcap
