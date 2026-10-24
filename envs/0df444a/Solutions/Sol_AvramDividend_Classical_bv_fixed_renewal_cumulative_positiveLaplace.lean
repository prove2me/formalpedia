-- Prove2me | solution 1 for AvramDividend.Classical.bv_fixed_renewal_cumulative_positiveLaplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:55:02.11783+00:00
-- url     : https://prove2.me/submissions/dff33012-df8e-40e9-8ee5-e06d85028dba

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_fixed_renewal_cumulative_positiveLaplace_canonical
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-!
A canonical-tilt fixed renewal measure witnesses the general existential
Esscher tilt theorem when bounded-variation drift is strictly positive.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ (β : Measure ℝ) (φ b : ℝ),
      0 < φ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      0 < β {0} ∧
      ∀ s : ℝ, b ≤ s →
        (∫⁻ x : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
        ENNReal.ofReal (1 / s) *
          ((ENNReal.ofReal X.drift)⁻¹ *
            (1 - (ENNReal.ofReal X.drift)⁻¹ *
              (∫⁻ z : ℝ≥0, ENNReal.ofReal
                ((1 - Real.exp (-(s + φ) * (z : ℝ))) / s)
                ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))))⁻¹) := by
  obtain ⟨β, b, hfin, hatom, htransform⟩ :=
    bv_fixed_renewal_cumulative_positiveLaplace_canonical
      X hX q hq hbv
  refine ⟨β, q / X.drift, b, div_pos hq
    (bv_standing_drift_pos X hX hbv).1, hfin, hatom, ?_⟩
  exact htransform
