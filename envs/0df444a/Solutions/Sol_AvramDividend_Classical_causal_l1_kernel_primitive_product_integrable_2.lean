-- Prove2me | solution 2 for AvramDividend.Classical.causal_l1_kernel_primitive_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T20:46:37.721968+00:00
-- url     : https://prove2.me/submissions/ec1cecb0-5a1f-4146-91c0-827464dbc367

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_causal_primitive_C1_locally_bounded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- An L1 causal kernel times a locally bounded causal primitive is integrable. -/
theorem solution
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun s : ℝ =>
      K (x - s) * (∫ t in Ioc (0 : ℝ) s, g t ∂volume))
      (Ioc (0 : ℝ) x) volume := by
  let G : ℝ → ℝ := fun s => ∫ t in Ioc (0 : ℝ) s, g t ∂volume
  obtain ⟨hGc, hGb⟩ := causal_primitive_C1_locally_bounded g hg
  have hKplus : Integrable ((Ioi (0 : ℝ)).indicator K) volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 hK
  have hshift : Integrable
      (fun s : ℝ => ((Ioi (0 : ℝ)).indicator K) (x - s)) volume :=
    hKplus.comp_sub_left x
  have hlocalIoo : IntegrableOn (fun s : ℝ => K (x - s))
      (Ioo (0 : ℝ) x) volume := by
    have hrestricted : IntegrableOn
        (fun s : ℝ => ((Ioi (0 : ℝ)).indicator K) (x - s))
        (Ioo (0 : ℝ) x) volume := hshift.integrableOn
    apply hrestricted.congr_fun _ measurableSet_Ioo
    intro s hs
    have hpos : (0 : ℝ) < x - s := sub_pos.mpr hs.2
    simp [Set.indicator_of_mem (show x - s ∈ Ioi (0 : ℝ) from hpos)]
  have hKl : IntegrableOn (fun s : ℝ => K (x - s))
      (Ioc (0 : ℝ) x) volume :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).2 hlocalIoo
  have hGcont : ContinuousOn G (Ioc (0 : ℝ) x) :=
    hGc.continuousOn.mono (by intro s hs; exact hs.1)
  have hGmeas : AEStronglyMeasurable G (volume.restrict (Ioc (0 : ℝ) x)) :=
    hGcont.aestronglyMeasurable measurableSet_Ioc
  obtain ⟨C, hC⟩ := hGb x hx
  have hbound : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) x), ‖G s‖ ≤ |C| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hsC := hC s hs
    exact le_trans (by simpa [G, Real.norm_eq_abs] using hsC) (le_abs_self C)
  have hprod : Integrable (fun s : ℝ => G s * K (x - s))
      (volume.restrict (Ioc (0 : ℝ) x)) :=
    hKl.bdd_mul hGmeas hbound
  change Integrable (fun s : ℝ => K (x - s) * G s)
    (volume.restrict (Ioc (0 : ℝ) x))
  simpa only [mul_comm] using hprod
