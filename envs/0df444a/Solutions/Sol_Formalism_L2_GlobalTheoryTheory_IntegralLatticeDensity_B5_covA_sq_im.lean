-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.covA_sq_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:40:08.483275+00:00
-- url     : https://prove2.me/submissions/158b3316-7c8e-4f22-a863-44acf155c966

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_LatITopBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Polynomial Matrix Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution (s : ℂ) (d : ℕ) (hd : 0 < d) (hs : s ^ 2 = -(d : ℂ)) :
    s.im ^ 2 = (d : ℝ) := by
  have h1 := congrArg Complex.re hs
  have h2 := congrArg Complex.im hs
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hre : s.re = 0 := by
    rcases mul_eq_zero.mp (show s.re * s.im = 0 by linarith) with h | h
    · exact h
    · rw [h] at h1
      nlinarith [sq_nonneg s.re]
  rw [hre] at h1
  nlinarith
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
