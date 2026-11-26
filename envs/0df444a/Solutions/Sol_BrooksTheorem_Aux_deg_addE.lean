-- Prove2me | solution 1 for BrooksTheorem.Aux.deg_addE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:38:14.096876+00:00
-- url     : https://prove2.me/submissions/59ed898b-0740-4360-843b-274604509237

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_addE_adj
public import Theorems.Thm_BrooksTheorem_Aux_nb_addE_sub
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
attribute [local simp] BrooksTheorem.Aux.mem_nb



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution {H : SimpleGraph V} {k : ℕ} (hdeg : ∀ v, (nb H v).card ≤ k) (S : Set V)
    {x z px pz : V} (hpx : H.Adj x px) (hpxS : px ∉ S) (hpz : H.Adj z pz) (hpzS : pz ∉ S) :
    ∀ v, (nb (restr H S ⊔ edge x z) v).card ≤ k := by
  classical
  intro v
  have aux : ∀ w w' pw, ((w = x ∧ w' = z) ∨ (w = z ∧ w' = x)) → H.Adj w pw → pw ∉ S →
      (nb (restr H S ⊔ edge x z) w).card ≤ k := by
    intro w w' pw hw hpw hpwS
    have h1 := card_le_card (nb_addE_sub H S hw hpwS)
    have h2 := card_insert_le w' ((nb H w).erase pw)
    have h3 := card_erase_of_mem (mem_nb.2 hpw)
    have h4 := hdeg w
    have h5 := card_pos.2 ⟨pw, mem_nb.2 hpw⟩
    omega
  by_cases hvx : v = x
  · exact hvx ▸ aux x z px (Or.inl ⟨rfl, rfl⟩) hpx hpxS
  by_cases hvz : v = z
  · exact hvz ▸ aux z x pz (Or.inr ⟨rfl, rfl⟩) hpz hpzS
  refine (card_le_card fun u hu => ?_).trans (hdeg v)
  rw [mem_nb, addE_adj] at hu
  rcases hu with hu | ⟨hu, _⟩
  · exact mem_nb.2 hu.1
  · exfalso; rcases hu with ⟨h1, _⟩ | ⟨h1, _⟩ <;> contradiction
end BrooksTheorem.Aux
