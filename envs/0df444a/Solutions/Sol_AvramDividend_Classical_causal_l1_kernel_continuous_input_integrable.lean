-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_kernel_continuous_input_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T19:10:57.448022+00:00
-- url     : https://prove2.me/submissions/8d8a481d-41a6-4944-90e0-13381501e527

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Group.Bounded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      IntegrableOn (fun s : ℝ => K (x - s) * g s) (Ioc (0 : ℝ) x) volume := by
  intro x hx
  have hKplus : Integrable ((Ioi (0 : ℝ)).indicator K) volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 hK
  have hshift : Integrable
      (fun s : ℝ => ((Ioi (0 : ℝ)).indicator K) (x - s)) volume :=
    hKplus.comp_sub_left x
  have hlocalIoo :
      IntegrableOn (fun s : ℝ => K (x - s)) (Ioo (0 : ℝ) x) volume := by
    have hrestricted : IntegrableOn
        (fun s : ℝ => ((Ioi (0 : ℝ)).indicator K) (x - s))
        (Ioo (0 : ℝ) x) volume := hshift.integrableOn
    apply hrestricted.congr_fun _ measurableSet_Ioo
    intro s hs
    have hpos : (0 : ℝ) < x - s := sub_pos.mpr hs.2
    simp [Set.indicator_of_mem (show x - s ∈ Ioi (0 : ℝ) from hpos)]
  have hlocalIoc :
      IntegrableOn (fun s : ℝ => K (x - s)) (Ioc (0 : ℝ) x) volume :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).2 hlocalIoo
  have hcont : ContinuousOn g (Icc (0 : ℝ) x) :=
    hg.mono (by intro s hs; exact hs.1)
  have hgi : IntegrableOn g (Ioc (0 : ℝ) x) volume :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) x)).exists_bound_of_continuousOn hcont
  have hbound : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) x), ‖g s‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hC s (Ioc_subset_Icc_self hs)
  have hprod : Integrable (fun s : ℝ => g s * K (x - s))
      (volume.restrict (Ioc (0 : ℝ) x)) :=
    hlocalIoc.bdd_mul hgi.aestronglyMeasurable hbound
  change Integrable (fun s : ℝ => K (x - s) * g s)
    (volume.restrict (Ioc (0 : ℝ) x))
  simpa only [mul_comm] using hprod
