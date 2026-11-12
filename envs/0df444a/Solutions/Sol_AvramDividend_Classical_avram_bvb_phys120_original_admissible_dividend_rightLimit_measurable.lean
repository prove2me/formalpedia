-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys120_original_admissible_dividend_rightLimit_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:10:22.049109+00:00
-- url     : https://prove2.me/submissions/db84055f-b68f-40e5-90fc-793a0d74bc52

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- The original right-limit dividend path is time-measurable, allowing
the physical stopped reserve and predictable jump kernels to be integrated. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) :
    Measurable (fun t : ℝ≥0 => rightLimit D t ω) := by
  have hmono : Monotone (fun s : ℝ≥0 => D s ω) := hD.1.1.2.1 ω
  have heq :
      (fun t : ℝ≥0 => rightLimit D t ω) =
        Function.rightLim (fun s : ℝ≥0 => D s ω) := by
    funext t
    calc
      rightLimit D t ω =
          sInf ((fun s : ℝ≥0 => D s ω) '' Ioi t) := by
            unfold rightLimit
            exact (sInf_image' (s := Ioi t)
              (f := fun s : ℝ≥0 => D s ω)).symm
      _ = Function.rightLim (fun s : ℝ≥0 => D s ω) t :=
        (hmono.rightLim_eq_sInf).symm
  rw [heq]
  exact hmono.rightLim.measurable
