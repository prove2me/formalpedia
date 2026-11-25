-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_lam1S_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:19:24.664891+00:00
-- url     : https://prove2.me/submissions/2d14f28b-2241-4319-bbcd-9c327b0de215

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_lam1S_le
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_withBot_le

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
    (F G : MvPolynomial (ι × Fin n) R) : lam1S LL S (F + G) ≤ max (lam1S LL S F) (lam1S LL S G) := by
  have key := flt_withBot_le (a := lam1S LL S (F + G)) (b := max (lam1S LL S F) (lam1S LL S G)) (N := 0) ?_
  · simpa using key
  intro M hM
  obtain ⟨h1, h2⟩ := max_le_iff.1 hM
  simp only [add_zero]
  rw [flt_lam1S_le] at h1 h2 ⊢
  rw [map_add]
  exact AddSubgroup.add_mem _ h1 h2
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
