-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.conj_mul_im_eq_normSq_mul_div_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:51:50.568397+00:00
-- url     : https://prove2.me/submissions/c47d8a17-b0cd-428b-bb69-66984bebcc61

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Jacobi
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_NormArea

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
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution (a b : ℂ) (ha : a ≠ 0) :
    ((starRingEnd ℂ) a * b).im = Complex.normSq a * (b / a).im := by
  have hn : Complex.normSq a ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
  rw [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  field_simp
  ring
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
