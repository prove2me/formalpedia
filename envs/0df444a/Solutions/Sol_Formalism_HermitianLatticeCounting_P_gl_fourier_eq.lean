-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gl_fourier_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:26.948798+00:00
-- url     : https://prove2.me/submissions/544efdd2-9954-4f64-96d7-e4085c944bc7

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (φ : ℂ → ℂ) (w : ℂ) :
    𝓕 φ w = ∫ c : ℂ, Complex.exp (2 * Complex.I *
      (((-(Complex.I * (π : ℂ) * (starRingEnd ℂ) w)) * c).im : ℂ)) * φ c := by
  rw [Real.fourier_eq']
  congr 1
  ext c
  rw [smul_eq_mul]
  congr 2
  have : ⟪c, w⟫ = c.re * w.re + c.im * w.im := by
    rw [Complex.inner]
    simp
    ring
  rw [this]
  simp only [Complex.mul_im, Complex.neg_im, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  push_cast
  ring
end Formalism.HermitianLatticeCounting.P
