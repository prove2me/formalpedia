-- Prove2me | solution 1 for Deduction.eq_ofReal_sub_of_dist_le_of_le_sub_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:18.474151+00:00
-- url     : https://prove2.me/submissions/f26e02df-c834-4b00-9be9-2c28b10f53ca

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauFinite
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauDichotomy

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
theorem _root_.solution {w : ℂ} {σ D : ℝ} (h1 : dist w (σ : ℂ) ≤ D) (h2 : D ≤ σ - w.re) :
    w = ((σ - D : ℝ) : ℂ) := by
  have hD0 : 0 ≤ D := dist_nonneg.trans h1
  rw [Complex.dist_eq_re_im, Complex.ofReal_re, Complex.ofReal_im] at h1
  have hq : (w.re - σ) ^ 2 + (w.im - 0) ^ 2 ≤ D ^ 2 := by
    have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ (w.re - σ) ^ 2 + (w.im - 0) ^ 2)
    have h0 := Real.sqrt_nonneg ((w.re - σ) ^ 2 + (w.im - 0) ^ 2)
    nlinarith
  have him : w.im = 0 := by nlinarith [sq_nonneg w.im]
  have hre : w.re = σ - D := by nlinarith [sq_nonneg w.im]
  apply Complex.ext
  · rw [Complex.ofReal_re]; exact hre
  · rw [Complex.ofReal_im]; exact him
end Deduction
