-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.prod_wP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:24.043875+00:00
-- url     : https://prove2.me/submissions/b2b1d687-493a-4547-95df-9e92ee510085

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {R L₂ : ℕ} {δ : ℝ}
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution (n : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.range n) :
    ∏ p ∈ Finset.range n, wP δ T p = δ ^ T.card * (1 - δ) ^ (n - T.card) := by
  unfold wP
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.range n).filter (fun x => x ∈ T) = T := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.1 (hT h), h⟩⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.range n) (fun x => x ∈ T)
  rw [h1, Finset.card_range] at h2
  rw [h1, show ((Finset.range n).filter (fun x => ¬ x ∈ T)).card = n - T.card by omega]
end Formalism.G0.TopsWeightFunctionBounds
