-- Prove2me | solution 1 for DeletionCode.RuleSetGraph.componentCount_rulesOfFamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:10:01.519752+00:00
-- url     : https://prove2.me/submissions/ee59ea99-21bd-41ad-99bf-bd2d3a8c2b03

import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_RuleSetGraph

set_option autoImplicit true
open DeletionCode DeletionCode.RuleSetGraph
open Windows HeaderRecovery GeneratingModel RootSelection
open SignedSupport RuleReconstruction SupportComponents
namespace DeletionCode.RuleSetGraph
theorem _root_.solution {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    componentCount (rulesOfFamily E group) =
      Fintype.card (GraphComponents E.family (windowLength k)) := by
  classical
  unfold componentCount
  rw [Nat.card_congr (ruleSetComponentEquiv E group hrank H hdis)]
  exact Nat.card_eq_fintype_card
end DeletionCode.RuleSetGraph
