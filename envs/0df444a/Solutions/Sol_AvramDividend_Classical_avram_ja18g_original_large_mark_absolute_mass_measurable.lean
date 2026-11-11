-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_large_mark_absolute_mass_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T03:30:01.028616+00:00
-- url     : https://prove2.me/submissions/fe10e543-8f71-4920-a7d2-de9844e9a470

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys55_original_intrinsic_NX_measure_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The physical absolute mark mass is measurable because the original marked
counting measure is measurable in its sample argument. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    ∀ t : ℝ≥0,
    Measurable (fun ω : Ω =>
      ∫⁻ p in (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)),
        ENNReal.ofReal |p.2| ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by
  intro t
  let B : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)
  let N (ω : Ω) : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let f : (ℝ≥0 × ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal |p.2|
  have hN : Measurable N := by
    simpa only [N] using
      (avram_bvb_phys55_original_intrinsic_NX_measure_measurable X)
  have hB : MeasurableSet B :=
    measurableSet_Ioc.prod measurableSet_Iic
  have hf : Measurable f :=
    ENNReal.measurable_ofReal.comp measurable_snd.abs
  have hInd : Measurable (B.indicator f) :=
    hf.indicator hB
  have hA : Measurable (fun ω : Ω =>
      ∫⁻ p, B.indicator f p ∂N ω) :=
    (Measure.measurable_lintegral hInd).comp hN
  change Measurable (fun ω : Ω => ∫⁻ p in B, f p ∂N ω)
  have hEq :
      (fun ω : Ω => ∫⁻ p in B, f p ∂N ω) =
      (fun ω : Ω => ∫⁻ p, B.indicator f p ∂N ω) := by
    funext ω
    exact (lintegral_indicator hB f).symm
  rw [hEq]
  exact hA
