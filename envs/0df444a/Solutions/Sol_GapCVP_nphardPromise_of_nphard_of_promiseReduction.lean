-- Prove2me | solution 1 for GapCVP.nphardPromise_of_nphard_of_promiseReduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/8f294812-788f-41db-ac96-a0f2acdd328a

import Mathlib
import Definitions.Def_GapCVP

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
namespace GapCVP
theorem _root_.solution
    {A : BitLanguage} {P : PromiseProblem} (hard : NPHard A)
    (reduction : PromiseReduction A P)
    (closed : PolynomialTimeClosedUnderComposition) : NPHardPromise P := by
  simp only [GapCVP.NPHardPromise, GapCVP.NPHard, GapCVP.IsNP, decide_eq_true_eq] at hard ⊢
  intro L hL
  obtain ⟨first⟩ := hard L hL
  exact ⟨PromiseReduction.comp first reduction closed⟩
end GapCVP
