-- Prove2me | solution 1 for ConfoundRobust.Minimax.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:10:37.516298+00:00
-- url     : https://prove2.me/submissions/8aa69bda-1dd3-4c6b-8dbd-291e9e8caa51

import Mathlib
import Definitions.Def_ConfoundRobust_Minimax_Setting

open MeasureTheory

theorem solution {α : Type*} (S : Set α) (h g : α → ℝ) (hS : S.Nonempty)
    (hh : BddAbove (h '' S)) (hg : BddAbove (g '' S))
    (hhg : BddAbove ((fun y => h y - g y) '' S)) :
    sSup (h '' S) - sSup (g '' S) ≤ sSup ((fun y => h y - g y) '' S) := by
  have key : sSup (h '' S) ≤ sSup ((fun y => h y - g y) '' S) + sSup (g '' S) := by
    apply csSup_le (hS.image h)
    rintro _ ⟨y, hy, rfl⟩
    have h1 : h y - g y ≤ sSup ((fun y => h y - g y) '' S) :=
      le_csSup hhg ⟨y, hy, rfl⟩
    have h2 : g y ≤ sSup (g '' S) := le_csSup hg ⟨y, hy, rfl⟩
    linarith
  linarith
