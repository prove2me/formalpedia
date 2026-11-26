-- Prove2me | solution 1 for Erdos338Proof.exists_multiset_of_mem_nsmul_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:47.609731+00:00
-- url     : https://prove2.me/submissions/22e0919a-daa7-4244-bc38-cff418b89f34

module
public import Mathlib
public import Definitions.Def_Erdos338_Kneser_Kneser
public import Definitions.Def_Erdos338_Covering

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open Erdos338Proof
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
namespace Erdos338Proof
theorem _root_.solution {f : ℕ →+ G} {A : Finset ℕ} :
    ∀ {h : ℕ} {z : G}, z ∈ h • A.image f →
      ∃ M : Multiset ℕ, M.card = h ∧ (∀ a ∈ M, a ∈ A) ∧ f M.sum = z := by
  intro h
  induction h with
  | zero =>
    intro z hz
    rw [zero_nsmul, Finset.mem_zero] at hz
    exact ⟨0, by simp, by simp, by simp [hz]⟩
  | succ n ih =>
    intro z hz
    rw [succ_nsmul, Finset.mem_add] at hz
    obtain ⟨x, hx, w, hw, rfl⟩ := hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨M, hMc, hMA, hMs⟩ := ih hx
    refine ⟨a ::ₘ M, by simp [hMc], ?_, ?_⟩
    · intro b hb
      rcases Multiset.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact hMA b hb
    · rw [Multiset.sum_cons, map_add, hMs, add_comm]
end Erdos338Proof
