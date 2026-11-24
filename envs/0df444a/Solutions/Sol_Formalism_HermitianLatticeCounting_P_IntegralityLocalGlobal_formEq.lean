-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal.formEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:17.011433+00:00
-- url     : https://prove2.me/submissions/1b61153a-11de-42b6-af38-717b4180d887

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ComplexMultiplicationRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open IntegralityLocalGlobal
open Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
namespace Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
theorem _root_.solution (a b c d : ℂ) (T T' : ℝ)
    (h : ∀ u v : ℂ, T * ‖a * u + b * v‖ ^ 2 - T' * ‖c * u + d * v‖ ^ 2 = T * ‖u‖ ^ 2 - T' * ‖v‖ ^ 2) :
    T ^ 2 * ‖b‖ ^ 2 = T' ^ 2 * ‖c‖ ^ 2 := by
  have h1 := h 1 0
  have h2 := h 0 1
  have h3 := h 1 1
  have h4 := h 1 Complex.I
  first
  | simp only [← Complex.normSq_eq_norm_sq] at h1 h2 h3 h4 ⊢
  | simp only [Complex.sq_norm] at h1 h2 h3 h4 ⊢
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, Complex.I_re,
    Complex.I_im] at h1 h2 h3 h4 ⊢
  linear_combination
    (T * (a.re * b.re + a.im * b.im) + T' * (c.re * d.re + c.im * d.im)) / 2 * (h3 - h1 - h2)
    + (T * (a.im * b.re - a.re * b.im) + T' * (c.im * d.re - c.re * d.im)) / 2 * (h4 - h1 - h2)
    - T * (b.re * b.re + b.im * b.im) * h1 - T' * (c.re * c.re + c.im * c.im) * h2
end Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
