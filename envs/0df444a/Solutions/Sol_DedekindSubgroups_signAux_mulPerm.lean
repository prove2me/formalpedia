-- Prove2me | solution 1 for DedekindSubgroups.signAux_mulPerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:06:56.107288+00:00
-- url     : https://prove2.me/submissions/117a9a20-bc41-41b9-b369-dc3bd184a7c9

module
public import Definitions.Def_DedekindSubgroups_Meyer
public import Definitions.Def_DedekindSubgroups_Parity
public import Theorems.Thm_DedekindSubgroups_sig_injOn
public import Theorems.Thm_DedekindSubgroups_inv_eq_card

set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution (hk : 0 < k) (hinv : h * h' % k = 1) :
    Perm.signAux (mulPerm hk hinv) = (-1) ^ inv h k := by
  unfold Perm.signAux
  rw [prod_ite, prod_const, prod_const_one, mul_one]
  congr 1
  rw [inv_eq_card]
  refine Finset.card_bij' (fun a _ => ((a.2 : ℕ), (a.1 : ℕ)))
    (fun p hp => ⟨⟨p.2, ?_⟩, ⟨p.1, ?_⟩⟩) ?_ ?_ ?_ ?_
  · simp only [invSet, mem_filter, mem_product, mem_range] at hp; exact hp.1.2
  · simp only [invSet, mem_filter, mem_product, mem_range] at hp; exact hp.1.1
  · rintro ⟨a, b⟩ ha
    simp only [mem_filter, Perm.mem_finPairsLT] at ha
    obtain ⟨hba, hle⟩ := ha
    simp only [invSet, mem_filter, mem_product, mem_range]
    refine ⟨⟨b.2, a.2⟩, hba, ?_⟩
    have hle' : sig h k a ≤ sig h k b := hle
    rcases lt_or_eq_of_le hle' with hlt | heq
    · exact hlt
    · exact absurd (sig_injOn hinv a.2 b.2 heq) (by
        have : (b : ℕ) < a := hba; omega)
  · rintro ⟨x, y⟩ hp
    simp only [invSet, mem_filter, mem_product, mem_range] at hp
    obtain ⟨⟨hx, hy⟩, hxy, hs⟩ := hp
    simp only [mem_filter, Perm.mem_finPairsLT]
    refine ⟨Fin.mk_lt_mk.mpr hxy, ?_⟩
    show sig h k y ≤ sig h k x
    exact le_of_lt hs
  · rintro ⟨a, b⟩ _; rfl
  · rintro ⟨x, y⟩ _; rfl
end DedekindSubgroups
