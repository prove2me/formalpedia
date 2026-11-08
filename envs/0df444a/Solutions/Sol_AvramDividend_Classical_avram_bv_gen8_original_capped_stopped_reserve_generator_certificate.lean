-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_original_capped_stopped_reserve_generator_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:57:20.021631+00:00
-- url     : https://prove2.me/submissions/40954edf-d3ec-4659-81d2-9811c56f7b77

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_vcstar_generator_zero_on_positive_closed_cap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped, capped post-payment reserves are BV generator-harmonic. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ cstar W)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (cstar W) D) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      let Z : ℝ := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      0 < Z →
        X.GeneratorIntegrable (vcstar W) Z ∧
          X.generator (vcstar W) Z - q * vcstar W Z = 0 := by
  intro ω t ht
  let Z : ℝ := Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  change 0 < Z → X.GeneratorIntegrable (vcstar W) Z ∧
      X.generator (vcstar W) Z - q * vcstar W Z = 0
  intro hpos
  have hb := avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
    X x (cstar W) hxc D hD ω t ht
  have hle : Z ≤ (cstar W).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (ne_of_lt hc)).mp hb.2
  exact avram_bv_gen8_vcstar_generator_zero_on_positive_closed_cap
    X hX hBV q hq W hW hc hcpos Z hpos hle
