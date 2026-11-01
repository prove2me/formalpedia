-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_original_prepayment_rightdrop_equals_stieltjes_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:45:23.975784+00:00
-- url     : https://prove2.me/submissions/f412a6ae-449c-42ae-a970-bd342a44e274

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_rightlim_payment_atom_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    dividendMeasure D ω {(t : ℝ)} =
      ENNReal.ofReal
        (riskProcess X x D t ω -
          Function.rightLim
            (fun s : ℝ≥0 => riskProcess X x D s ω) t) := by
  rw [dividendMeasure_singleton_eq_rightLimit_sub D hD ω t,
    (avram_wave4_p2_original_prepayment_rightlim_payment_atom_exact
      X x D hD ω t).1]
  change ENNReal.ofReal (rightLimit D t ω - D t ω) =
    ENNReal.ofReal
      ((x + X.X t ω - D t ω) -
        (x + X.X t ω - rightLimit D t ω))
  congr 1
  ring