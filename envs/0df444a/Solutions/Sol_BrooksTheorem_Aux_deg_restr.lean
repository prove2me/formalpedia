-- Prove2me | solution 1 for BrooksTheorem.Aux.deg_restr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:38:01.874774+00:00
-- url     : https://prove2.me/submissions/44ec7493-9e26-4161-a1cd-ed0462231ddd

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_nb_restr_subset

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution {H : SimpleGraph V} {k : ℕ} (hdeg : ∀ v, (nb H v).card ≤ k) (S : Set V) :
    ∀ v, (nb (restr H S) v).card ≤ k :=
  fun v => (card_le_card (nb_restr_subset H S v)).trans (hdeg v)
end BrooksTheorem.Aux
