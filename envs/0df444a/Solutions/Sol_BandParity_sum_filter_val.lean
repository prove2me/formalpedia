-- Prove2me | solution 1 for BandParity.sum_filter_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:04:09.06631+00:00
-- url     : https://prove2.me/submissions/2e795940-899f-42e9-beda-7f46bf84bdee

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution {R : Type*} [AddCommMonoid R] (P : ℕ → Prop) [DecidablePred P]
    (g : ℕ → R) :
    ∑ x ∈ univ.filter (fun x : ZMod p => P x.val), g x.val =
      ∑ v ∈ (range p).filter P, g v := by
  refine Finset.sum_nbij (fun x => x.val) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and, mem_range] at hx ⊢
    exact ⟨ZMod.val_lt x, hx⟩
  · intro x _ y _ h; exact ZMod.val_injective p h
  · intro v hv
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hv
    refine ⟨(v : ZMod p), ?_, ZMod.val_natCast_of_lt hv.1⟩
    simp [ZMod.val_natCast_of_lt hv.1, hv.2]
  · intro _ _; rfl
end BandParity
