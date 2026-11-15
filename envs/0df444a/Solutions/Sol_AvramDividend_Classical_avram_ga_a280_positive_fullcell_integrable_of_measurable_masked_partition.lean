-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a280_positive_fullcell_integrable_of_measurable_masked_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:21:58.215664+00:00
-- url     : https://prove2.me/submissions/9e701080-1fdb-41f6-a40b-f69f34b1af3c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F S L : Ω → ℝ)
    (hFm : AEStronglyMeasurable (fun ω => max (F ω) 0) P)
    (hSi : Integrable (fun ω => max (S ω) 0) P)
    (hLi : Integrable (fun ω => max (L ω) 0) P)
    (hPt : ∀ ω, max (F ω) 0 ≤ max (S ω) 0+max (L ω) 0) :
    Integrable (fun ω => max (F ω) 0) P := by
  have hDom : Integrable
      (fun ω => max (S ω) 0+max (L ω) 0) P :=
    hSi.add hLi
  apply Integrable.mono' hDom hFm
  filter_upwards [] with ω
  have hf : 0 ≤ max (F ω) 0 := le_max_right _ _
  have hs : 0 ≤ max (S ω) 0 := le_max_right _ _
  have hl : 0 ≤ max (L ω) 0 := le_max_right _ _
  have hh := hPt ω
  simpa only [Real.norm_eq_abs,Pi.add_apply,
    abs_of_nonneg hf,abs_of_nonneg (add_nonneg hs hl)] using hh
