-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ShearCoefficients.CoeffHom.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:10:38.374149+00:00
-- url     : https://prove2.me/submissions/9dd02bd6-e246-4ba5-8ae0-7ec6ed935989

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
theorem _root_.solution {m : M} {P Q : Polynomial (MvPolynomial σ R)} (hP : CoeffHom wt m P)
    (hQ : CoeffHom wt m Q) : CoeffHom wt m (P + Q) := by
  intro k; rw [Polynomial.coeff_add]; exact (hP k).add (hQ k)
end CoeffHom
end Formalism.NormUnitaryCountingLemmas.ShearCoefficients
