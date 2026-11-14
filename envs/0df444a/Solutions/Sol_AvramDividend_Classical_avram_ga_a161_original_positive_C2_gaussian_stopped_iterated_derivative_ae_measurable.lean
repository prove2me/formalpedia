-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a161_original_positive_C2_gaussian_stopped_iterated_derivative_ae_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:45:59.200866+00:00
-- url     : https://prove2.me/submissions/c4e6d583-1a37-4e6a-af1d-70995dc8378c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 2 w (Ioi (0 : ℝ)))
    (k : ℕ) (hk : k ≤ 2)
    (Y : Ω → ℝ) (hY : Measurable Y)
    (hPos : ∀ᵐ ω ∂P, 0 < Y ω) :
    AEStronglyMeasurable
      (fun ω => iteratedDeriv k w (Y ω)) P := by
  classical
  have hOpen : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
  have hContWithin : ContinuousOn
      (iteratedDerivWithin k w (Ioi (0 : ℝ))) (Ioi (0 : ℝ)) :=
    hw.continuousOn_iteratedDerivWithin (by exact_mod_cast hk)
      hOpen.uniqueDiffOn
  have hCont : ContinuousOn (iteratedDeriv k w) (Ioi (0 : ℝ)) := by
    have hEq : EqOn (iteratedDerivWithin k w (Ioi (0 : ℝ)))
        (iteratedDeriv k w) (Ioi (0 : ℝ)) :=
      iteratedDerivWithin_of_isOpen hOpen
    exact hContWithin.congr hEq.symm
  have hMeas : Measurable
      ((Ioi (0 : ℝ)).piecewise (iteratedDeriv k w) (fun _ => (0 : ℝ))) :=
    ContinuousOn.measurable_piecewise hCont continuousOn_const hOpen.measurableSet
  refine (aestronglyMeasurable_congr ?_).mp ((hMeas.comp hY).aestronglyMeasurable)
  filter_upwards [hPos] with ω hω
  simp [Set.piecewise, hω]
