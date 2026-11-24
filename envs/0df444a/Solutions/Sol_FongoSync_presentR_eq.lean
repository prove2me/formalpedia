-- Prove2me | solution 1 for FongoSync.presentR_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:03.837129+00:00
-- url     : https://prove2.me/submissions/afac5a11-3a9a-45b5-bd9a-dfa047ff6b82

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
import Theorems.Thm_FongoSync_namesLiveB_iff
import Theorems.Thm_FongoSync_liveNow_iff
import Theorems.Thm_FongoSync_liveMembersR_eq

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution : presentR sc inp = present sc inp := by
  have hlive : ∀ m, liveNow sc inp m = true ↔ Live sc inp m := liveNow_iff sc inp
  funext r
  unfold presentR present
  have hg : ∀ f, groupEntryR sc inp f r = groupEntry sc inp f r := by
    intro f; unfold groupEntryR groupEntry; rw [liveMembersR_eq]
  have hr : ∀ f e, readR sc inp f e = read sc inp f e := by
    intro f e
    cases e with
    | none => rfl
    | some e =>
      simp only [readR, read]
      cases f.kind <;> simp only
      all_goals
        cases e.value <;> simp only
        rename_i o
        by_cases h : namesLive inp (Live sc inp) o
        · simp [h, (namesLiveB_iff inp hlive o).mpr h]
        · have : namesLiveB inp (liveNow sc inp) o = false := by
            cases hb : namesLiveB inp (liveNow sc inp) o
            · rfl
            · exact absurd ((namesLiveB_iff inp hlive o).mp hb) h
          simp [h, this]
  simp only [hg, hr]
  by_cases h : ∃ m ∈ inp.gids, inp.canon m = r ∧ Live sc inp m
  · have : (inp.gids.any fun m => inp.canon m == r && liveNow sc inp m) = true := by
      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, hlive]; exact h
    simp [h, this]
  · have : (inp.gids.any fun m => inp.canon m == r && liveNow sc inp m) = false := by
      simp only [List.any_eq_false, Bool.and_eq_true, beq_iff_eq, hlive]
      intro m hm ⟨hc, hl⟩; exact h ⟨m, hm, hc, hl⟩
    simp [h, this]
end FongoSync
