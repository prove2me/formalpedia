-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ShearCoefficients.comp_coeff_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:43:11.881921+00:00
-- url     : https://prove2.me/submissions/19a83573-7594-4c1a-a38b-0ce7f8fab955

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_CoeffHom_add
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_coeffHom_shear_monomial

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
theorem _root_.solution {N n : ℕ} (i j : Fin N) (w : Fin n → ℕ)
    (F : MvPolynomial (Fin N × Fin n) R) (k : ℕ) :
    weightedHomogeneousComponent (coordWt N n) w ((shear R i j F).coeff k) =
      (shear R i j (weightedHomogeneousComponent (coordWt N n) w F)).coeff k := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [weightedHomogeneousComponent_of_mem (coeffHom_shear_monomial i j d r k),
      weightedHomogeneousComponent_of_mem
        (isWeightedHomogeneous_monomial (coordWt N n) d r rfl)]
    split_ifs <;> simp
  | add p q hp hq =>
    rw [map_add, map_add, Polynomial.coeff_add, map_add, hp, hq, map_add, Polynomial.coeff_add]
end Formalism.NormUnitaryCountingLemmas.ShearCoefficients
