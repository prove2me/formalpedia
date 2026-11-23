-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G3.phase1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:40.005651+00:00
-- url     : https://prove2.me/submissions/6ec67b5b-e2b7-44e6-b7f8-b00493daca7e

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G3
namespace Formalism.FourierDecayAlt.P.G3
theorem _root_.solution (β ξ v : ℂ) :
    -2 * Real.pi * ⟪v, al β * (starRingEnd ℂ) ξ⟫ = (β * (ξ * v)).re := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [Complex.inner]
  unfold al
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  field_simp
  ring
end Formalism.FourierDecayAlt.P.G3
