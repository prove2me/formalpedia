-- Prove2me | solution 1 for AvramDividend.Classical.zero_reflectedSupValue_of_unbounded_ae_no_local_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:01:01.245023+00:00
-- url     : https://prove2.me/submissions/352eb25e-86c5-4af7-a47f-69d29da72626

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_no_local_monotone_path
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_unbounded_instant_ruin
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Transfer local path non-monotonicity to the proved instant-ruin identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hNoMono : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ¬ MonotoneOn (fun t : ℝ≥0 => X.X t ω) (Icc 0 ε)) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by
  have hruin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0 :=
    hNoMono.mono (fun ω hω =>
      barrierRuinTime_zero_of_no_local_monotone_path X ω hω)
  exact zero_reflectedSupValue_of_unbounded_instant_ruin
    X q hq W hW hnbv hruin
