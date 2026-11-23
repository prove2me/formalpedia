-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G3.phase2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:39.992986+00:00
-- url     : https://prove2.me/submissions/b7a68af8-ad7a-4636-a369-b3de1f2bfd02

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
theorem _root_.solution (β ξ w : ℂ) :
    2 * Real.pi * ⟪al β * (starRingEnd ℂ) ξ, -w⟫ = (β * (w * ξ)).re := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [Complex.inner]
  unfold al
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, map_mul, map_neg, Complex.conj_conj,
    Complex.conj_ofReal]
  field_simp
  ring
end Formalism.FourierDecayAlt.P.G3
