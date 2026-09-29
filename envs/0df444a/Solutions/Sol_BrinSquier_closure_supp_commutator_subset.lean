-- Prove2me | solution 1 for BrinSquier.closure_supp_commutator_subset
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-13T07:41:55.629407+00:00
-- url     : https://prove2.me/submissions/83ec6e83-a8c1-48e9-ab35-c11a7a9ef865

import Theorems.Thm_BrinSquier_commutator_id_near_common_fixed
import Definitions.Def_BrinSquier
import Mathlib

open BrinSquier

theorem solution {f g : ℝ ≃o ℝ} (hf : IsPLF f) (hg : IsPLF g) :
    closure (supp (f * g * f⁻¹ * g⁻¹)) ⊆ supp f ∪ supp g := by
  intro t ht
  by_contra hout
  simp only [Set.mem_union, not_or] at hout
  obtain ⟨ε, hε, hid⟩ :=
    BrinSquier.commutator_id_near_common_fixed hf hg (not_not.1 hout.1) (not_not.1 hout.2)
  have hnb : Set.Ioo (t - ε) (t + ε) ∩ supp (f * g * f⁻¹ * g⁻¹) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact hy.2 (hid y hy.1)
  have hne := mem_closure_iff.mp ht (Set.Ioo (t - ε) (t + ε)) isOpen_Ioo ⟨by linarith, by linarith⟩
  rw [Set.nonempty_iff_ne_empty] at hne
  exact hne hnb
