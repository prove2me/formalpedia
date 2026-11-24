-- Prove2me | solution 1 for FongoSync.rule_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:43.411799+00:00
-- url     : https://prove2.me/submissions/2cde32ab-dd6e-494c-96a2-372d265b2627

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution {p q : Gid → Prop} (h : ∀ m ∈ inp.gids, p m ↔ q m) (g : Gid) :
    rule sc inp p g ↔ rule sc inp q g := by
  have hn : namesLive inp p = namesLive inp q := by
    funext o
    apply propext
    simp only [namesLive]
    constructor
    · rintro ⟨ho, m, hm, hc, hp⟩; exact ⟨ho, m, hm, hc, (h m hm).mp hp⟩
    · rintro ⟨ho, m, hm, hc, hq⟩; exact ⟨ho, m, hm, hc, (h m hm).mpr hq⟩
  have ho : ownerAllows inp p = ownerAllows inp q := by
    funext v
    cases v with
    | none => rfl
    | some e => simp only [ownerAllows, hn]
  simp only [rule, ho]
end FongoSync
