-- Prove2me | solution 1 for Expanders.card_level_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:29:32.886185+00:00
-- url     : https://prove2.me/submissions/f8021c46-a71a-452a-a88a-92ea17cd038f

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] {d k : ℕ} (B : Finset V) (h : V → ℕ)
namespace Expanders
theorem _root_.solution (hd : G.IsRegularOfDegree d)
    (hstep : ∀ v ∈ B, ∀ w ∈ B, G.Adj v w → h w ≤ h v + 1)
    (hpar : ∀ v ∈ B, ∃ w ∈ B, G.Adj v w ∧ h w ≤ h v - 1) (i : ℕ) :
    (B.filter (fun v => h v = i + 1)).card ≤ (B.filter (fun v => h v = i)).card * (d - 1) := by
  classical
  have := Finset.card_mul_le_card_mul (fun a b => G.Adj a b)
    (s := B.filter (fun v => h v = i + 1)) (t := B.filter (fun v => h v = i)) (m := 1)
    (n := d - 1) ?_ ?_
  · simpa using this
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨w, hwB, haw, hw⟩ := hpar a ha.1
    have h1 := hstep w hwB a ha.1 haw.symm
    apply Finset.card_pos.mpr
    refine ⟨w, ?_⟩
    rw [Finset.mem_bipartiteAbove, Finset.mem_filter]
    exact ⟨⟨hwB, by omega⟩, haw⟩
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨w0, hw0B, hbw0, hw0⟩ := hpar b hb.1
    have hsub : Finset.bipartiteBelow (fun a b => G.Adj a b) (B.filter (fun v => h v = i + 1)) b
        ⊆ (G.neighborFinset b).erase w0 := by
      intro a ha
      rw [Finset.mem_bipartiteBelow, Finset.mem_filter] at ha
      rw [Finset.mem_erase, mem_neighborFinset]
      refine ⟨?_, ha.2.symm⟩
      rintro rfl
      omega
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_erase_of_mem (by simpa using hbw0), card_neighborFinset_eq_degree, hd b]
end Expanders
