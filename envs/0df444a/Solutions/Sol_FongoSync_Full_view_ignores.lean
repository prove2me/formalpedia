-- Prove2me | solution 1 for FongoSync.Full.view_ignores
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:59:28.828339+00:00
-- url     : https://prove2.me/submissions/482b0e1e-017d-444c-8be6-07a5f4df2d27

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
namespace FongoSync.Full
theorem _root_.solution (sc : Schema) (c : Change Value) (cs : List (Change Value))
    (h : ¬ (c.clock.encodable ∧ aliasOk c = true ∧ (sc.find c.collection).isSome)) :
    view sc (c :: cs) = view sc cs := by
  have hc : candidates sc (c :: cs) = candidates sc cs := by
    simp only [candidates, List.filter_cons]
    have : (decide c.clock.encodable && aliasOk c && (sc.find c.collection).isSome) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases h₁ : c.clock.encodable
      · by_cases h₂ : aliasOk c = true
        · exact .inr (by simpa [h₁, h₂] using h)
        · exact .inl (.inr (by simpa using h₂))
      · exact .inl (.inl h₁)
    simp [this]
  simp only [view, hc]
end FongoSync.Full
