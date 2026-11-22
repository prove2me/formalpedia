-- Prove2me | solution 1 for ConfFamily.esRStep_bwd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:04:14.327303+00:00
-- url     : https://prove2.me/submissions/b3472b2d-f59c-4260-978c-edad3f63b69e

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Stable_LTSI
import Theorems.Thm_ConfFamily_union_diff_singleton

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
variable {F}
namespace ConfFamily
theorem _root_.solution {c c' : Conf F} {a : L} {e : F.Event}
    (hc : F.Config c'.val) (he : e ∈ c.val) (hlbl : F.label e = a)
    (htgt : c'.val = c.val \ {e}) : esRStep F c (DirLabel.bwd a) c' :=
  ⟨e, ⟨hc, by rw [htgt, union_diff_singleton he]; exact c.2⟩,
   by rw [htgt]; exact fun h => h.2 rfl, hlbl,
   by rw [htgt, union_diff_singleton he]⟩
end ConfFamily
