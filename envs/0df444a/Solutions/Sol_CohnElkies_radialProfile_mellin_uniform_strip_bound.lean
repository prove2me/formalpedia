-- Prove2me | solution 1 for CohnElkies.radialProfile_mellin_uniform_strip_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/b9116476-3995-4561-bd43-944bcca40a35

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialProfile_mellinConvergent

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, 0 ≤ s.re → s.re ≤ (d : ℝ) →
        ‖mellin (radialProfile hd f) s‖ ≤ C := by
  have hmeas :
      AEStronglyMeasurable (radialProfile hd f)
        (volume.restrict (Ioi (0 : ℝ))) :=
    (radialProfile_continuous hd f).aestronglyMeasurable
  have hzeroWeight : IntegrableOn
      (fun r : ℝ => r ^ (-(1 : ℝ)) *
        ‖radialProfile hd f r‖) (Ioi (0 : ℝ)) := by
    have hconv := radialProfile_mellinConvergent
      hd f hf hzero (0 : ℂ) (by norm_num)
    simpa using!
      (mellin_convergent_iff_norm
        (T := Ioi (0 : ℝ)) Subset.rfl
        measurableSet_Ioi hmeas).mp hconv
  have hdimensionWeight : IntegrableOn
      (fun r : ℝ => r ^ ((d : ℝ) - 1) *
        ‖radialProfile hd f r‖) (Ioi (0 : ℝ)) := by
    have hre : -2 < ((d : ℂ).re) := by
      norm_num
      linarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]
    have hconv := radialProfile_mellinConvergent
      hd f hf hzero (d : ℂ) hre
    simpa using!
      (mellin_convergent_iff_norm
        (T := Ioi (0 : ℝ)) Subset.rfl
        measurableSet_Ioi hmeas).mp hconv
  have hmajor : IntegrableOn
      (fun r : ℝ =>
        (r ^ (-(1 : ℝ)) + r ^ ((d : ℝ) - 1)) *
          ‖radialProfile hd f r‖) (Ioi (0 : ℝ)) := by
    simpa [Pi.add_apply, add_mul] using!
      hzeroWeight.add hdimensionWeight
  let B : ℝ :=
    ∫ r : ℝ in Ioi (0 : ℝ),
      (r ^ (-(1 : ℝ)) + r ^ ((d : ℝ) - 1)) *
        ‖radialProfile hd f r‖
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro s hs hsd
  have hconv : MellinConvergent (radialProfile hd f) s :=
    radialProfile_mellinConvergent hd f hf hzero s (by linarith)
  have hbound : ‖mellin (radialProfile hd f) s‖ ≤ B := by
    calc
      ‖mellin (radialProfile hd f) s‖ ≤
          ∫ r : ℝ in Ioi (0 : ℝ),
            ‖(r : ℂ) ^ (s - 1) • radialProfile hd f r‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ r : ℝ in Ioi (0 : ℝ),
          (r ^ (-(1 : ℝ)) + r ^ ((d : ℝ) - 1)) *
            ‖radialProfile hd f r‖ := by
        apply integral_mono_ae hconv.norm hmajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        change 0 < r at hr
        rw [norm_smul,
          Complex.norm_cpow_eq_rpow_re_of_pos hr]
        norm_num
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        by_cases hone : r ≤ 1
        · calc
            r ^ (s.re - 1) ≤ r ^ (-(1 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_ge hr hone
                (by linarith)
            _ ≤ r ^ (-(1 : ℝ)) + r ^ ((d : ℝ) - 1) := by
              exact le_add_of_nonneg_right
                (Real.rpow_nonneg hr.le _)
        · have hlarge : 1 ≤ r := le_of_not_ge hone
          calc
            r ^ (s.re - 1) ≤ r ^ ((d : ℝ) - 1) :=
              Real.rpow_le_rpow_of_exponent_le hlarge
                (by linarith)
            _ ≤ r ^ (-(1 : ℝ)) + r ^ ((d : ℝ) - 1) := by
              exact le_add_of_nonneg_left
                (Real.rpow_nonneg hr.le _)
      _ = B := rfl
  exact hbound.trans (le_max_right _ _)
end CohnElkies
