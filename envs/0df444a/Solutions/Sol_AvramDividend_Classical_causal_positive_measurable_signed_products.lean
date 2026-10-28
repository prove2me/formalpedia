-- Prove2me | solution 1 for AvramDividend.Classical.causal_positive_measurable_signed_products
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T16:26:16.472+00:00
-- url     : https://prove2.me/submissions/5a39ad04-566f-48d5-a3f7-a5063ded5d3c

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Positive-time continuity makes signed causal products measurable off a null endpoint. -/
theorem solution
    (k : ℝ → ℝ) (P : ℕ → ℝ → ℝ)
    (hkcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hPcont : ∀ n : ℕ, ContinuousOn (P n) (Ioi (0 : ℝ))) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      AEStronglyMeasurable
        (fun s : ℝ => k (x - s) * P n s)
        (volume.restrict (Ioc (0 : ℝ) x)) := by
  intro n x hx
  have hmap : MapsTo (fun s : ℝ => x - s) (Ioo (0 : ℝ) x) (Ioi (0 : ℝ)) := by
    intro s hs
    exact sub_pos.mpr hs.2
  have hk : ContinuousOn (fun s : ℝ => k (x - s)) (Ioo (0 : ℝ) x) :=
    hkcont.comp (continuous_const.sub continuous_id).continuousOn hmap
  have hp : ContinuousOn (P n) (Ioo (0 : ℝ) x) :=
    (hPcont n).mono (by
      intro s hs
      exact hs.1)
  have hprod : ContinuousOn (fun s : ℝ => k (x - s) * P n s)
      (Ioo (0 : ℝ) x) := hk.mul hp
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => k (x - s) * P n s)
      (volume.restrict (Ioo (0 : ℝ) x)) :=
    hprod.aestronglyMeasurable measurableSet_Ioo
  simpa only [restrict_Ioo_eq_restrict_Ioc] using hmeas
