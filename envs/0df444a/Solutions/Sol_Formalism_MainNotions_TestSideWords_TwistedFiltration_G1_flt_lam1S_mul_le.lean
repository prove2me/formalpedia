-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_lam1S_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:18:19.956297+00:00
-- url     : https://prove2.me/submissions/98bdf08e-810a-426e-8379-b21a387ab37f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_lam1S_le
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_withBot_le_add

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
    (F G : MvPolynomial (ι × Fin n) R) : lam1S LL S (F * G) ≤ lam1S LL S F + lam1S LL S G := by
  apply flt_withBot_le_add
  intro t u ht hu
  rw [flt_lam1S_le] at ht hu ⊢
  rw [map_mul]
  have := (laurentCoeffFiltration R n (ι × Fin n) (-1)).mul_mem ht hu
  rwa [show -(t + u) = -t + -u by ring]
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
