-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SecondPolynomialClauses.herm_of_psd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:48.468809+00:00
-- url     : https://prove2.me/submissions/3a1cacd9-b619-4752-b09d-489f3d1fc313

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SecondPolynomialClauses
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.SecondPolynomialClauses
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (R : Formalism.FourierDecayAlt.F7.Sesq V) (hR : PSD R)
    (x y : V) : (starRingEnd ℂ) (R x y) = R y x := by
  have h1 := (hR (x + y)).1
  have h2 := (hR (x + Complex.I • y)).1
  have hx := (hR x).1
  have hy := (hR y).1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, map_smulₛₗ, Complex.conj_I,
    smul_eq_mul] at h1 h2
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im] at h1 h2
  apply Complex.ext
  · simp only [Complex.conj_re]; nlinarith
  · simp only [Complex.conj_im]; nlinarith
end Formalism.FourierDecayAlt.P.SecondPolynomialClauses
