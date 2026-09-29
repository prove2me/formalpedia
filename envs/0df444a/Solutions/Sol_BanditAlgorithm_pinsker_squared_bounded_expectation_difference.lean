-- Prove2me | solution 1 for BanditAlgorithm.pinsker_squared_bounded_expectation_difference
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T23:31:47.160497+00:00
-- url     : https://prove2.me/submissions/158999e2-06aa-42a2-9fc0-711abf794c1e

import Theorems.Thm_BanditAlgorithm_pinsker_squared_event_difference
import Mathlib.MeasureTheory.Integral.Layercake

open MeasureTheory InformationTheory Real Set
open scoped ENNReal

namespace BanditAlgorithm

theorem _root_.solution {Omega : Type} {mOmega : MeasurableSpace Omega}
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Omega → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hD : klDiv P Q ≠ ∞) :
    2 * ((∫ x, f x ∂Q) - ∫ x, f x ∂P) ^ 2 ≤ (klDiv P Q).toReal := by
  have hf_int (M : Measure Omega) [IsProbabilityMeasure M] : Integrable f M := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
      exact hf1 x
  have htail_meas (M : Measure Omega) :
      Measurable (fun t : ℝ ↦ M.real {x | t ≤ f x}) := by
    apply Measurable.ennreal_toReal
    apply Antitone.measurable
    intro s t hst
    exact measure_mono fun x hx ↦ hst.trans hx
  have htail_int (M : Measure Omega) [IsProbabilityMeasure M] :
      Integrable (fun t : ℝ ↦ M.real {x | t ≤ f x})
        (volume.restrict (Ioc 0 1)) := by
    apply Integrable.of_bound (htail_meas M).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun t ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc
        M.real {x | t ≤ f x} ≤ M.real Set.univ := by
          exact ENNReal.toReal_mono (measure_ne_top M Set.univ)
            (measure_mono (Set.subset_univ _))
        _ = 1 := by simp
  have hreprM (M : Measure Omega) [IsProbabilityMeasure M] :
      ∫ x, f x ∂M = ∫ t in Ioc (0 : ℝ) 1, M.real {x | t ≤ f x} := by
    exact (hf_int M).integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hf1)
  rw [hreprM Q, hreprM P, ← integral_sub (htail_int Q) (htail_int P)]
  let D : ℝ := (klDiv P Q).toReal
  let C : ℝ := Real.sqrt (D / 2)
  have hD0 : 0 ≤ D := by positivity
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  have hpoint (t : ℝ) :
      ‖Q.real {x | t ≤ f x} - P.real {x | t ≤ f x}‖ ≤ C := by
    have hset : MeasurableSet {x | t ≤ f x} :=
      measurableSet_le measurable_const hf
    have hsquare := pinsker_squared_event_difference P Q hset hD
    have hCsq : C ^ 2 = D / 2 := by
      exact Real.sq_sqrt (by positivity)
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (Q.real {x | t ≤ f x} - P.real {x | t ≤ f x})]
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (C := C) (Filter.Eventually.of_forall hpoint)
  have hmass : (volume.restrict (Ioc (0 : ℝ) 1)).real Set.univ = 1 := by
    simp
  rw [hmass, mul_one] at hnorm
  rw [Real.norm_eq_abs] at hnorm
  have hsq :
      (∫ t in Ioc (0 : ℝ) 1,
          (Q.real {x | t ≤ f x} - P.real {x | t ≤ f x})) ^ 2 ≤ C ^ 2 := by
    let z := ∫ t in Ioc (0 : ℝ) 1,
      (Q.real {x | t ≤ f x} - P.real {x | t ≤ f x})
    have hprod : 0 ≤ (C - |z|) * (C + |z|) :=
      mul_nonneg (sub_nonneg.mpr hnorm) (add_nonneg hC0 (abs_nonneg z))
    dsimp [z] at hprod ⊢
    nlinarith [sq_abs (∫ t in Ioc (0 : ℝ) 1,
      (Q.real {x | t ≤ f x} - P.real {x | t ≤ f x}))]
  rw [show C ^ 2 = D / 2 by exact Real.sq_sqrt (by positivity)] at hsq
  dsimp [D] at hsq ⊢
  linarith

end BanditAlgorithm
