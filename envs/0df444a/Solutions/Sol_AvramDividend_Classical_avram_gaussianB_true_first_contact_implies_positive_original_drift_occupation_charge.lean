-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_true_first_contact_implies_positive_original_drift_occupation_charge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:10:54.336315+00:00
-- url     : https://prove2.me/submissions/28238586-7b9b-4e9b-a440-799f8577f563

import Mathlib.Topology.Instances.NNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_first_contact_time_equal_horizon_forces_upper_strip_occupation
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_NNReal_first_contact_floor_real_physical_times
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_strict_positive_drift_charge_on_full_upper_strip
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal
noncomputable section
/-- Original first-contact clock forces an omitted strictly positive drift occupation term. -/
theorem solution
    (f : ℝ≥0 → ℝ) (b c : ℝ) (T : ℝ≥0)
    (hT : 0 < T) (hc : 0 < c)
    (hFirst : sInf ((Icc (0 : ℝ≥0) T ∩ (fun t : ℝ≥0 => -(f t)) ⁻¹' Ici (-b)) ∪ {T}) = T) :
    0 < c * ∫ t in Ioo (0 : ℝ) (T : ℝ),
      (if b < f (Real.toNNReal t) then (1 : ℝ) else 0) ∂volume := by
  have hFloor :
      ∀ t : ℝ≥0, t < T → b < f t :=
    avram_gaussianB_first_contact_time_equal_horizon_forces_upper_strip_occupation
      f b T hFirst
  have hReal :
      ∀ u : ℝ, 0 < u → u < (T : ℝ) →
        b < f (Real.toNNReal u) :=
    avram_gaussianB_NNReal_first_contact_floor_real_physical_times
      f T b hFloor
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  exact
    avram_gaussianB_strict_positive_drift_charge_on_full_upper_strip
      c (T : ℝ) b hc hTreal
      (fun u : ℝ => f (Real.toNNReal u)) hReal
