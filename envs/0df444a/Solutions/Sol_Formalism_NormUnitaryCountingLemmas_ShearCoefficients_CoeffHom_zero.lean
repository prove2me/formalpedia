-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ShearCoefficients.CoeffHom.zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:36.631775+00:00
-- url     : https://prove2.me/submissions/812ec0b3-9bb7-45c4-8f9e-8904beedc5c6

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.ShearCoefficients
variable {R : Type*} [CommRing R]
variable {σ M : Type*} [AddCommMonoid M] {wt : σ → M}
namespace Formalism.NormUnitaryCountingLemmas.ShearCoefficients
namespace CoeffHom
theorem _root_.solution (m : M) : CoeffHom (R := R) wt m 0 := by
  intro k; rw [Polynomial.coeff_zero]; exact isWeightedHomogeneous_zero R wt m
end CoeffHom
end Formalism.NormUnitaryCountingLemmas.ShearCoefficients
