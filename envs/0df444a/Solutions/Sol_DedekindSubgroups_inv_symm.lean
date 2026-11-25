-- Prove2me | solution 1 for DedekindSubgroups.inv_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:06:53.382673+00:00
-- url     : https://prove2.me/submissions/17069697-51d3-48c1-9a8a-752e846e9409

module
public import Definitions.Def_DedekindSubgroups_Meyer
public import Definitions.Def_DedekindSubgroups_Parity
public import Theorems.Thm_DedekindSubgroups_inv_eq_card

set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution (hk : 0 < k) (hinv : h * h' % k = 1) : inv h' k = inv h k := by
  have hinv' : h' * h % k = 1 := by rwa [mul_comm]
  rw [inv_eq_card, inv_eq_card]
  refine Finset.card_nbij' (fun p => (sig h' k p.2, sig h' k p.1))
    (fun p => (sig h k p.2, sig h k p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [invSet, coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨⟨hx, hy⟩, hxy, hs⟩ := hp
    refine ⟨⟨sig_lt hk _ _, sig_lt hk _ _⟩, hs, ?_⟩
    rw [sig_sig hinv' hx, sig_sig hinv' hy]; exact hxy
  · rintro ⟨x, y⟩ hp
    simp only [invSet, coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp ⊢
    obtain ⟨⟨hx, hy⟩, hxy, hs⟩ := hp
    refine ⟨⟨sig_lt hk _ _, sig_lt hk _ _⟩, hs, ?_⟩
    rw [sig_sig hinv hx, sig_sig hinv hy]; exact hxy
  · rintro ⟨x, y⟩ hp
    simp only [invSet, coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp
    obtain ⟨⟨hx, hy⟩, _, _⟩ := hp
    simp [sig_sig hinv' hx, sig_sig hinv' hy]
  · rintro ⟨x, y⟩ hp
    simp only [invSet, coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp
    obtain ⟨⟨hx, hy⟩, _, _⟩ := hp
    simp [sig_sig hinv hx, sig_sig hinv hy]
end DedekindSubgroups
