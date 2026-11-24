-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.T_mem_laurentFiltration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:08:44.422368+00:00
-- url     : https://prove2.me/submissions/576b0b56-ae10-4933-b65a-af343fe82590

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_L_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution {A : Type*} [CommRing A] (e k : ℤ) : (LaurentPolynomial.T k : LaurentPolynomial A) ∈ (flt_L A e).F (e * k) := by
  rw [flt_L_mem]
  intro k' hk
  rw [LaurentPolynomial.T_apply] at hk
  split_ifs at hk with h
  · rw [h]
  · exact absurd rfl hk
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
