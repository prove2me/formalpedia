-- Prove2me | solution 1 for C6BipartiteDomination.card_liftFinsetToSubtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:01:46.792799+00:00
-- url     : https://prove2.me/submissions/7a35aca5-efdd-46de-bdaa-0b7134b23d0f

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults

set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {S E : Finset V} (hES : E ⊆ S) :
    (liftFinsetToSubtype S E hES).card = E.card := by
  classical
  unfold liftFinsetToSubtype
  have hinj : Function.Injective
      (fun x : {v // v ∈ E} => (⟨x.1, hES x.2⟩ : {v // v ∈ S})) := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {v // v ∈ S} => z.1) h
  rw [Finset.card_image_of_injective E.attach hinj]
  simp
end C6BipartiteDomination
