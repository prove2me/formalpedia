-- Prove2me | solution 1 for FongoSync.liveCount_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:05:46.904014+00:00
-- url     : https://prove2.me/submissions/6c188011-56e1-4863-aee9-d87849330f7d

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
import Theorems.Thm_FongoSync_liveAt_succ_of
import Theorems.Thm_FongoSync_length_filter_lt

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution {k : Nat} (h : ¬ ∀ g ∈ inp.gids, liveAt sc inp (k + 1) g → liveAt sc inp k g) :
    liveCount sc inp k < liveCount sc inp (k + 1) := by
  apply length_filter_lt
  · intro x _ hx; simpa using liveAt_succ_of sc inp (by simpa using hx)
  · simp only [Classical.not_forall] at h
    obtain ⟨g, hg, h1, h2⟩ := h
    exact ⟨g, hg, by simpa using h1, by simpa using h2⟩
end FongoSync
