-- Prove2me | solution 1 for Deduction.iteratedDeriv_laplace_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:52.143466+00:00
-- url     : https://prove2.me/submissions/5b622577-f9e5-464d-bfc4-6fdbab1845ae

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_IteratedDerivLaplace
import Theorems.Thm_Deduction_iteratedDeriv_laplace_int
import Theorems.Thm_Deduction_iteratedDeriv_laplace_meas
import Theorems.Thm_Deduction_iteratedDeriv_laplace_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)) (k : ℕ) (s : ℂ) (hs : 2 < s.re) :
    HasDerivAt (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u))
      (∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ (k + 1) * cexp (-s * u)) s := by
  set δ := (s.re - 2) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hre : ∀ z ∈ Metric.ball s δ, 2 + δ ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - s)
    rw [Complex.sub_re] at h1
    have h2 := (abs_le.mp (h1.trans hz.le)).1
    linarith
  have hint : Integrable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-s * u))
      (volume.restrict (Ioi 0)) := by
    refine Integrable.mono' (Integrable.const_mul (iteratedDeriv_laplace_int k δ hδpos) C)
      (iteratedDeriv_laplace_meas g hg k s) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    exact iteratedDeriv_laplace_bound g C hgC k δ s (hre s (Metric.mem_ball_self hδpos)) u hu
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z u => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u))
    (F' := fun z u => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ (k + 1) * cexp (-z * u))
    (Metric.ball_mem_nhds s hδpos)
    (Eventually.of_forall fun z => iteratedDeriv_laplace_meas g hg k z) hint
    (iteratedDeriv_laplace_meas g hg (k + 1) s) ?_
    (Integrable.const_mul (iteratedDeriv_laplace_int (k + 1) δ hδpos) C) ?_).2
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu z hz => ?_)
    exact iteratedDeriv_laplace_bound g C hgC (k + 1) δ z (hre z hz) u hu
  · refine Eventually.of_forall fun u z _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => -w * (u : ℂ)) (-(u : ℂ)) z := by
      simpa using (hasDerivAt_id' z).neg.mul_const (u : ℂ)
    have h2 := h1.cexp.const_mul ((g u : ℂ) * ((-u : ℝ) : ℂ) ^ k)
    refine h2.congr_deriv ?_
    push_cast
    ring
end Deduction
