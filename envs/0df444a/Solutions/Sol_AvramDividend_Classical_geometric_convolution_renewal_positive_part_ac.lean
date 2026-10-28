-- Prove2me | solution 1 for AvramDividend.Classical.geometric_convolution_renewal_positive_part_ac
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T18:47:16.55358+00:00
-- url     : https://prove2.me/submissions/bc7a5ed5-3c1e-4616-8146-de9d00e04986

import Theorems.Thm_AvramDividend_Classical_renewal_measure_ac_on_positive
import Theorems.Thm_AvramDividend_Classical_positive_geometric_renewal_measure_package
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- The non-atomic part of a geometric convolution renewal sum is Lebesgue-AC. -/
theorem solution
    (κ : Measure ℝ) [SFinite κ]
    (hκac : κ ≪ (volume : Measure ℝ))
    (m : ℕ → Measure ℝ)
    (hm0 : m 0 = Measure.dirac (0 : ℝ))
    (hmsucc : ∀ n : ℕ, m (n + 1) = Measure.conv κ (m n))
    (hsf : ∀ n : ℕ, SFinite (m n))
    (c : ℝ≥0∞) :
    (Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)).restrict (Ioi (0 : ℝ)) ≪
      (volume : Measure ℝ) := by
  have hpos (n : ℕ) : m (n + 1) ≪ (volume : Measure ℝ) := by
    letI : SFinite (m n) := hsf n
    rw [hmsucc n, Measure.conv_comm]
    exact Measure.conv_absolutelyContinuous hκac
  refine Measure.AbsolutelyContinuous.mk (fun s hs hnull => ?_)
  rw [Measure.restrict_apply hs]
  rw [Measure.sum_apply _ (hs.inter measurableSet_Ioi)]
  have hterm (n : ℕ) :
      (c ^ (n + 1) • m n) (s ∩ Ioi (0 : ℝ)) = 0 := by
    cases n with
    | zero =>
        rw [hm0]
        simp [Measure.smul_apply, Measure.dirac_apply' _ (hs.inter measurableSet_Ioi)]
    | succ n =>
        have hzero : m (n + 1) (s ∩ Ioi (0 : ℝ)) = 0 :=
          hpos n (measure_mono_null inter_subset_left hnull)
        simp [Measure.smul_apply, hzero]
  simp [hterm]
