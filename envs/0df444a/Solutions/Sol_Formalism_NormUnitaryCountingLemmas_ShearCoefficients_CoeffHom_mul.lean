-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ShearCoefficients.CoeffHom.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:35.610582+00:00
-- url     : https://prove2.me/submissions/c0b97a3a-ea90-4875-85cb-709e4b5220f8

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
theorem _root_.solution {a b : M} {P Q : Polynomial (MvPolynomial σ R)} (hP : CoeffHom wt a P)
    (hQ : CoeffHom wt b Q) : CoeffHom wt (a + b) (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ (fun x _ => (hP x.1).mul (hQ x.2))
end CoeffHom
end Formalism.NormUnitaryCountingLemmas.ShearCoefficients
