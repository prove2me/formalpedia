-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_cost_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:08:46.012839+00:00
-- url     : https://prove2.me/submissions/b3ff1f72-3671-48f6-82c1-2060b6958506

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical

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
open Classical
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (b : Bool) (v : ι × Fin n) (k : ℕ) :
    flt_cost LL S b (Finsupp.single v k) = if v.1 ∈ S ∧ LL.vec v.1 = b then (k : ℤ) else 0 := by
  unfold flt_cost
  rw [Finsupp.liftAddHom_apply_single]
  split_ifs
  · rfl
  · rfl
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
