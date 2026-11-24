-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_valS_mul_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:23.04203+00:00
-- url     : https://prove2.me/submissions/a4d501de-8760-4e30-9a68-7cc72951002d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_le_valS
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_withTop_add_le

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
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : valS LL S F + valS LL S G ≤ valS LL S (F * G) := by
  apply flt_withTop_add_le
  intro t u ht hu
  rw [flt_le_valS] at ht hu ⊢
  rw [map_mul]
  exact (laurentCoeffFiltration R n (ι × Fin n) 1).mul_mem ht hu
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
