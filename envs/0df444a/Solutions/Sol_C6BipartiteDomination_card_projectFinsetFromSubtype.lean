-- Prove2me | solution 1 for C6BipartiteDomination.card_projectFinsetFromSubtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:37.295394+00:00
-- url     : https://prove2.me/submissions/81a853f9-5165-46d4-ac26-76cbae3b7ce7

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {S : Finset V}
    (F : Finset {v // v ∈ S}) :
    (projectFinsetFromSubtype (S := S) F).card = F.card := by
  classical
  unfold projectFinsetFromSubtype
  have hinj : Function.Injective (fun x : {v // v ∈ S} => x.1) := by
    intro x y h
    exact Subtype.ext h
  exact Finset.card_image_of_injective F hinj
end C6BipartiteDomination
