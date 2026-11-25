-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.hasWt2_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:54:29.251623+00:00
-- url     : https://prove2.me/submissions/77a9f2cb-41d8-47c8-978a-85b0c908eedf

import Definitions.Def_Formalism_FrobeniusBaseCase_CoeffOfFirstMultiplier
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
variable {k : Type*} [Field k] {Z Z' : Type*} {v : AddValuation k (WithTop ℝ)}
namespace Formalism.BaseCaseIdentities
theorem _root_.solution {r r' w : ℝ} {f : MvPowerSeries (Z ⊕ Z') k} :
    HasWt2 v r r' w f ↔ HasWtG v (om2 Z Z' r r') w f := by
  constructor
  · intro h E
    have h1 := h (Finsupp.sumFinsuppAddEquivProdFinsupp E).1
      (Finsupp.sumFinsuppAddEquivProdFinsupp E).2
    have h2 : Finsupp.sumElim (Finsupp.sumFinsuppAddEquivProdFinsupp E).1
        (Finsupp.sumFinsuppAddEquivProdFinsupp E).2 = E :=
      Finsupp.sumFinsuppAddEquivProdFinsupp.symm_apply_apply E
    rw [h2] at h1
    exact h1
  · intro h A B
    have h1 := h (Finsupp.sumElim A B)
    have h2 : Finsupp.sumFinsuppAddEquivProdFinsupp (Finsupp.sumElim A B) = (A, B) :=
      Finsupp.sumFinsuppAddEquivProdFinsupp.apply_symm_apply (A, B)
    have h3 : om2 Z Z' r r' (Finsupp.sumElim A B) =
        ((A.degree : ℕ) : ℝ) * r + ((B.degree : ℕ) : ℝ) * r' := by
      show (((Finsupp.sumFinsuppAddEquivProdFinsupp (Finsupp.sumElim A B)).1.degree : ℕ) : ℝ) * r +
        (((Finsupp.sumFinsuppAddEquivProdFinsupp (Finsupp.sumElim A B)).2.degree : ℕ) : ℝ) * r' = _
      rw [h2]
    rw [h3] at h1
    exact h1
end Formalism.BaseCaseIdentities
