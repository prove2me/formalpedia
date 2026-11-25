-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ShearCoefficients.perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:22:13.565533+00:00
-- url     : https://prove2.me/submissions/12533a57-0897-46d5-bbf9-e9a6cf773a1f

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_mem_H_iff
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_isWeightedHomogeneous_rename
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_shear_rename_perm

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
theorem _root_.solution : NormUnitaryPermutationInvariance := by
  intro R _ N n ν σ F hF
  rw [mem_H_iff] at hF ⊢
  refine ⟨isWeightedHomogeneous_rename hF.1, fun i j hij => ?_⟩
  rw [shear_rename_perm, hF.2 i j hij, Polynomial.map_C]
  rfl
end Formalism.NormUnitaryCountingLemmas.ShearCoefficients
