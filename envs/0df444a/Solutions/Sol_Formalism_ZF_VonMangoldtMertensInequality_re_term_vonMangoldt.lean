-- Prove2me | solution 1 for Formalism.ZF.VonMangoldtMertensInequality.re_term_vonMangoldt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:11.043259+00:00
-- url     : https://prove2.me/submissions/a275f50e-2246-4379-9bf4-121db72a4c66

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ThreeFourOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.VonMangoldtMertensInequality
namespace Formalism.ZF.VonMangoldtMertensInequality
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) (σ y : ℝ) :
    (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + y * I) n).re =
      Λ n * Real.exp (-σ * Real.log n) * Real.cos (y * Real.log n) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, Complex.re_ofReal_mul,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), Complex.exp_re]
  have hre : (Complex.log (n : ℂ)).re = Real.log n := by
    rw [Complex.log_re, Complex.norm_natCast]
  have him : (Complex.log (n : ℂ)).im = 0 := by
    rw [Complex.log_im, Complex.natCast_arg]
  simp only [Complex.mul_re, Complex.mul_im, hre, him, Complex.neg_re, Complex.neg_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [mul_assoc]
  congr 2
  · congr 1
    ring
  · rw [← Real.cos_neg]
    congr 1
    ring
end Formalism.ZF.VonMangoldtMertensInequality
