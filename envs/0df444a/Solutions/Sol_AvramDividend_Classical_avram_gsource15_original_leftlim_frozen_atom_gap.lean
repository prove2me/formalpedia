-- Prove2me | solution 1 for AvramDividend.Classical.avram_gsource15_original_leftlim_frozen_atom_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:48:13.249628+00:00
-- url     : https://prove2.me/submissions/54a39fa0-5619-4fc8-9b9e-1847c8bc9054

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hXleft : Function.leftLim (fun s : ℝ≥0 => X.X s ω) t = X.X t ω) :
    Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      (x + X.X t ω - rightLimit D t ω) +
        (rightLimit D t ω - D t ω) := by
  rw [avram_wave3_04_postPaymentReserve_exact_leftLim_identity
    X x D hD ω t ht, hXleft]
  ring
