-- Prove2me | solution 1 for Erdos1219.exists_fiber_eq_of_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:18.514824+00:00
-- url     : https://prove2.me/submissions/4e240de2-e467-47dd-856d-a60060f73a85

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Theorems.Thm_Erdos1219_mk_iUnion_lt_of_isRegular

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution {V T : Type u} {c : Cardinal.{u}} (hc : c.IsRegular)
    (s : Set V) (hs : #s = c) (φ : V → T) (hT : #T < c) :
    ∃ t, #(s ∩ φ ⁻¹' {t} : Set V) = c := by
  by_contra h
  have hlt : ∀ t, #(s ∩ φ ⁻¹' {t} : Set V) < c := fun t =>
    lt_of_le_of_ne ((mk_le_mk_of_subset Set.inter_subset_left).trans_eq hs)
      (fun ht => h ⟨t, ht⟩)
  have hsub : s ⊆ ⋃ t, s ∩ φ ⁻¹' {t} := fun v hv => Set.mem_iUnion.2 ⟨φ v, hv, rfl⟩
  exact absurd ((mk_le_mk_of_subset hsub).trans_lt (mk_iUnion_lt_of_isRegular hc hT _ hlt))
    (by rw [hs]; exact lt_irrefl c)
end Erdos1219
