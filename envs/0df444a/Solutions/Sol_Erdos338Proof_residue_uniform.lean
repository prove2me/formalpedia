-- Prove2me | solution 1 for Erdos338Proof.residue_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:48.448574+00:00
-- url     : https://prove2.me/submissions/121d251a-36c4-4c83-8212-dff9066bd235

module
public import Mathlib
public import Definitions.Def_Erdos338_Residue

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution {A : Set ℕ} {Q : ℕ} (hQ : 0 < Q)
    (hres : ∀ c, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ ∑ x ∈ S, x ≡ c [MOD Q]) :
    ∃ B T : ℕ, ∀ c, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ #S ≤ B ∧ ∑ x ∈ S, x ≤ T ∧
      ∑ x ∈ S, x ≡ c [MOD Q] := by
  choose f hfA hf using hres
  refine ⟨(range Q).sup fun c ↦ #(f c), (range Q).sup fun c ↦ ∑ x ∈ f c, x,
    fun c ↦ ⟨f (c % Q), hfA _, ?_, ?_, ?_⟩⟩
  · exact le_sup (f := fun c ↦ #(f c)) (mem_range.2 (Nat.mod_lt c hQ))
  · exact le_sup (f := fun c ↦ ∑ x ∈ f c, x) (mem_range.2 (Nat.mod_lt c hQ))
  · exact (hf _).trans (Nat.mod_modEq c Q)
end Erdos338Proof
