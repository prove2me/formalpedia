-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_filtration_past_future_indepFun_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T18:56:01.282828+00:00
-- url     : https://prove2.me/submissions/4af3ea47-c1b7-4df7-984f-bf31fe222570

import Mathlib
import Mathlib.Probability.Process.Filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- Independence of the original past-filtration sigma algebra from the
future marked increment's generated sigma algebra implies independence of
*any* measurable past observable, including tuples of controlled coefficients
and accumulated compensated prefixes, from that future increment. -/
theorem solution
    {Ω ι E F : Type*} [mΩ : MeasurableSpace Ω]
    [Preorder ι] [mE : MeasurableSpace E]
    [mF : MeasurableSpace F]
    (𝓕 : Filtration ι mΩ) (i : ι) (P : Measure Ω)
    (Z : Ω → E) (W : Ω → F)
    (hInd : Indep (𝓕 i) (MeasurableSpace.comap Z mE) P)
    (hW : Measurable[𝓕 i] W) :
    IndepFun W Z P := by
  exact (IndepFun_iff_Indep W Z P).2
    (indep_of_indep_of_le_left hInd hW.comap_le)
