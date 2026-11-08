-- Prove2me | solution 1 for DarkKnights.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:29:06.287976+00:00
-- url     : https://prove2.me/submissions/c3aeb791-038c-4fac-92a2-8d269f73ae82

import Mathlib
import Definitions.Def_DarkKnights_Primitives

open DarkKnights in
theorem solution (a b bn h : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbn : 0 ≤ bn) (hbnb : bn ≤ b)
    (hh : 0 ≤ h) :
    (bn ≤ h * b →
      (a < bn → defaultAction a bn (h * b) = Action.liquidate) ∧
      (bn ≤ a → defaultAction a bn (h * b) = Action.repay)) ∧
    (h * b < bn →
      (a < h * b → defaultAction a bn (h * b) = Action.liquidate) ∧
      (h * b ≤ a → defaultAction a bn (h * b) = Action.renegotiate)) := by
  refine ⟨fun hc => ⟨fun ha' => ?_, fun ha' => ?_⟩, fun hc => ⟨fun ha' => ?_, fun ha' => ?_⟩⟩
  · unfold defaultAction
    rw [if_neg (fun h1 => by linarith [h1.1]), if_neg (fun h2 => by linarith [h2.1])]
  · unfold defaultAction
    rw [if_pos ⟨by linarith, fun _ => by linarith⟩]
  · unfold defaultAction
    rw [if_neg (fun h1 => by linarith [h1.1]), if_neg (fun h2 => by linarith [h2.1])]
  · unfold defaultAction
    rw [if_neg (fun h1 => by linarith [h1.2 ha'])]
    rw [if_pos ⟨ha', by linarith⟩]
