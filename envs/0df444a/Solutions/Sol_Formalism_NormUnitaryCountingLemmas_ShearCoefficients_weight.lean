-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ShearCoefficients.weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:56:37.009806+00:00
-- url     : https://prove2.me/submissions/e80fa884-dabc-40a0-b7c7-9b5ffb756d63

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_mem_H_iff
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_comp_coeff_shear

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
theorem _root_.solution : NormUnitaryWeight := by
  classical
  intro R _ N n ν F hF w
  rw [mem_H_iff] at hF ⊢
  refine ⟨?_, fun i j hij => ?_⟩
  · intro d hd
    rw [coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd
    · exact hF.1 hd
    · exact absurd rfl hd
  · refine Polynomial.ext fun k => ?_
    rw [← comp_coeff_shear, hF.2 i j hij, Polynomial.coeff_C, Polynomial.coeff_C]
    split_ifs <;> simp
end Formalism.NormUnitaryCountingLemmas.ShearCoefficients
