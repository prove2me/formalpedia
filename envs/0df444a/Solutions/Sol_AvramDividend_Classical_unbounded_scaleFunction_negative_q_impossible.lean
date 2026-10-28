-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scaleFunction_negative_q_impossible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:07:16.544701+00:00
-- url     : https://prove2.me/submissions/42da0973-1322-4923-afd5-b5446235b975

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A strictly positive monotone scale function cannot have a finite
unweighted Laplace integral on the positive half-line. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : q < 0)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) : False := by
  have hqψ : q < X.ψ 0 := by
    rw [levy_laplace_exponent_zero X]
    exact hq
  have hInt : IntegrableOn W (Ioi (0 : ℝ)) := by
    simpa using (hW.2.2.2.2 0 (le_refl _) hqψ).1
  have hWone : 0 < W 1 :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv 1 (by norm_num)
  have hTail : IntegrableOn W (Ioi (1 : ℝ)) := by
    exact hInt.mono_set (by
      intro x hx
      exact lt_trans (by norm_num : (0 : ℝ) < 1) hx)
  have hMono : MonotoneOn W (Ici (0 : ℝ)) := hW.2.2.2.1
  have hConst : IntegrableOn (fun _ : ℝ => W 1) (Ioi (1 : ℝ)) := by
    apply Integrable.mono_nonneg hTail
    · fun_prop
    · exact Filter.Eventually.of_forall (fun _ => le_of_lt hWone)
    · exact (ae_restrict_mem measurableSet_Ioi).mono (fun x hx =>
        hMono (by norm_num : (1 : ℝ) ∈ Ici 0)
          (by exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hx))
          (le_of_lt hx))
  rcases (integrable_const_iff.mp hConst) with hz | hfinite
  · exact (ne_of_gt hWone) hz
  · letI : IsFiniteMeasure (volume.restrict (Ioi (1 : ℝ))) := hfinite
    have hmeasure : (volume.restrict (Ioi (1 : ℝ))) Set.univ < ⊤ :=
      measure_lt_top (volume.restrict (Ioi (1 : ℝ))) Set.univ
    have hbad : (volume : Measure ℝ) (Ioi 1) < ⊤ := by
      simpa using hmeasure
    rw [Real.volume_Ioi] at hbad
    exact (lt_irrefl (⊤ : ℝ≥0∞)) hbad
