-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys119_original_dividend_rightLimit_eq_strict_rightLim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:09:42.121198+00:00
-- url     : https://prove2.me/submissions/c2654bd6-bd21-4dd1-9995-20d6e83acd4b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- Original infimum-defined rightLimit equals the Mathlib strict
right limit of each monotone admissible dividend path at every time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    rightLimit D t ω =
      Function.rightLim (fun s : ℝ≥0 => D s ω) t := by
  have hmono : Monotone (fun s : ℝ≥0 => D s ω) := hD.1.1.2.1 ω
  calc
    rightLimit D t ω =
        sInf ((fun s : ℝ≥0 => D s ω) '' Ioi t) := by
          unfold rightLimit
          exact (sInf_image' (s := Ioi t)
            (f := fun s : ℝ≥0 => D s ω)).symm
    _ = Function.rightLim (fun s : ℝ≥0 => D s ω) t :=
      (hmono.rightLim_eq_sInf).symm
