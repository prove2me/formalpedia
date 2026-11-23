-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ShearCoefficients.CoeffHom.one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:12.283847+00:00
-- url     : https://prove2.me/submissions/d90bd455-019c-4f8b-a25d-b91a37f4bb5b

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
theorem _root_.solution : CoeffHom (R := R) wt 0 1 := by
  simpa using CoeffHom.C (R := R) (isWeightedHomogeneous_one R wt)
end CoeffHom
end Formalism.NormUnitaryCountingLemmas.ShearCoefficients
