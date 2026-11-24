-- Prove2me | solution 1 for FongoSync.liveB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:05:39.961785+00:00
-- url     : https://prove2.me/submissions/6e9bd717-7891-4e59-93d0-0c7a5c591dd9

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
import Theorems.Thm_FongoSync_deletedB_iff
import Theorems.Thm_FongoSync_ownerAllowsB_iff

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution (k : Nat) (g : Gid) : liveB sc inp k g = true ↔ liveAt sc inp k g := by
  induction k generalizing g with
  | zero => simp [liveB, liveAt]
  | succ k ih =>
    simp only [liveB, liveAt, Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem,
      Bool.not_eq_true', ih, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
    rw [← deletedB_iff]
    simp only [Bool.not_eq_true]
    constructor
    · rintro (h | ⟨⟨hm, hd⟩, hf⟩)
      · exact .inl h
      · refine .inr ⟨hm, hd, fun f hf' hk => ?_⟩
        rcases hf f hf' with h | h
        · exact absurd hk h
        · exact (ownerAllowsB_iff inp ih _).mp h
    · rintro (h | ⟨hm, hd, hf⟩)
      · exact .inl h
      · refine .inr ⟨⟨hm, hd⟩, fun f hf' => ?_⟩
        by_cases hk : f.kind = .owner
        · exact .inr ((ownerAllowsB_iff inp ih _).mpr (hf f hf' hk))
        · exact .inl hk
end FongoSync
