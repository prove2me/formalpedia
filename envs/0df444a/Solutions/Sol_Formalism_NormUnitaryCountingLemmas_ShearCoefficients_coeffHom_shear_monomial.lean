-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ShearCoefficients.coeffHom_shear_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:34:19.098368+00:00
-- url     : https://prove2.me/submissions/448202db-26d5-4ff4-a985-5363c62bce3e

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_CoeffHom_mul
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_CoeffHom_pow
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_CoeffHom_prod
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_coeffHom_shear_X

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
namespace Formalism.NormUnitaryCountingLemmas.ShearCoefficients
theorem _root_.solution {N n : ℕ} (i j : Fin N) (d : (Fin N × Fin n) →₀ ℕ) (r : R) :
    CoeffHom (coordWt N n) (Finsupp.weight (coordWt N n) d) (shear R i j (monomial d r)) := by
  rw [shear, aeval_monomial, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum,
    ← zero_add (∑ a ∈ d.support, d a • coordWt N n a)]
  refine CoeffHom.mul ?_ (CoeffHom.prod _ _ _ fun p _ => (coeffHom_shear_X i j p).pow _)
  rw [Polynomial.algebraMap_apply]
  exact CoeffHom.C (isWeightedHomogeneous_C _ _)
end Formalism.NormUnitaryCountingLemmas.ShearCoefficients
