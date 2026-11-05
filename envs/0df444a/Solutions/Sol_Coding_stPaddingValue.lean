-- Prove2me | solution 1 for Coding.stPaddingValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:07:43.714341+00:00
-- url     : https://prove2.me/submissions/a58a6688-0602-45d7-ad5d-f2d314b98217

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Definitions.Def_Coding_Padding
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Eight.SecNetworks
namespace Coding
theorem _root_.solution : StPaddingValue := by
  intro g N₀ N pad h
  constructor
  · classical
    unfold Net.value
    have hinj : Set.InjOn (fun (z : Fin g → List Bool) a => pad a (z a)) (Fintype.piFinset N₀.S) := by
      intro z hz z' hz' e
      funext a
      exact h.inj a (z a) (Fintype.mem_piFinset.1 (Finset.mem_coe.1 hz) a) (z' a) (Fintype.mem_piFinset.1 (Finset.mem_coe.1 hz') a) (congrFun e a)
    have hsub : (Fintype.piFinset N₀.S).image (fun z a => pad a (z a)) ⊆ Fintype.piFinset N.S := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
      exact Fintype.mem_piFinset.2 fun a => h.maps a _ (Fintype.mem_piFinset.1 hz a)
    rw [← Finset.sum_subset hsub, Finset.sum_image hinj]
    · refine Finset.sum_congr rfl fun z hz => ?_
      have hz' := Fintype.mem_piFinset.1 hz
      congr 1
      · exact Finset.prod_congr rfl fun a _ => h.W a _ (hz' a)
      · exact Finset.prod_congr rfl fun p hp => h.Ψ p.1 p.2 (ne_of_lt (Finset.mem_filter.1 hp).2) _ (hz' _) _ (hz' _)
    · intro y hy hny
      obtain ⟨a, ha⟩ : ∃ a, ∀ z ∈ N₀.S a, pad a z ≠ y a := by
        by_contra hcon
        push Not at hcon
        choose z hz hzy using hcon
        exact hny (Finset.mem_image.2 ⟨z, Fintype.mem_piFinset.2 hz, funext hzy⟩)
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (h.off a _ (Fintype.mem_piFinset.1 hy a) ha), zero_mul]
  · unfold Net.U
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => h.c a b (Finset.ne_of_mem_erase hb).symm
end Coding
