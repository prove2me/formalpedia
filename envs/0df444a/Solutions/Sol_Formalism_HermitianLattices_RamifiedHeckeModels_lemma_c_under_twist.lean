-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedHeckeModels.lemma_c_under_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:09:38.180529+00:00
-- url     : https://prove2.me/submissions/dab757e1-87ab-4f8e-b6aa-a974e06de1bf

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LengthQuotientLeOfLatticeSandwich
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Theorems.Thm_Formalism_HermitianLattices_RamifiedHeckeModels_length_quotient_bound_general

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedHeckeModels
open Formalism.HermitianLattices.LocalLatticeBases Finset ComplexConjugate
open Formalism.LogVandermondeBounds.product_first_zeroth_parts Module
namespace Formalism.HermitianLattices.RamifiedHeckeModels
theorem _root_.solution : LemmaC_twist := by
  intro R _ _ _ ϖ hϖ M _ _ S B U D e b hSB hU hD hUD _ _
  have hmap : (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).map U = S.map ((ϖ ^ b) • U) := by
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp
  rw [← hmap]
  exact length_quotient_bound_general ϖ hϖ S _ B U D e hSB hU hD hUD
end Formalism.HermitianLattices.RamifiedHeckeModels
