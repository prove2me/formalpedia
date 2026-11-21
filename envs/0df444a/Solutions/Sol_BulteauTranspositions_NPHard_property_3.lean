-- Prove2me | solution 1 for BulteauTranspositions.NPHard.property_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:20:32.782416+00:00
-- url     : https://prove2.me/submissions/b33205d5-c60e-4a57-95f4-b3c6cd9911cf

import Definitions.Def_BulteauTranspositions_NPHard_Sorting

namespace Aux_BulteauTranspositions_NPHard_property_3

open BulteauTranspositions.NPHard

theorem tau_cases (c : Cut) (y : ℕ) :
    (y < c.i ∧ c.tau y = y) ∨
    (c.i ≤ y ∧ y < c.k + c.i - c.j ∧ c.tau y = y + c.j - c.i) ∨
    (c.i ≤ y ∧ c.k + c.i - c.j ≤ y ∧ y < c.k ∧ c.tau y = y + c.j - c.k) ∨
    (c.i ≤ y ∧ c.k + c.i - c.j ≤ y ∧ c.k ≤ y ∧ c.tau y = y) := by
  unfold Cut.tau
  split_ifs <;> omega

theorem inv_i (c : Cut) : c.inv.i = c.i := rfl
theorem inv_j (c : Cut) : c.inv.j = c.k + c.i - c.j := rfl
theorem inv_k (c : Cut) : c.inv.k = c.k := rfl

theorem tau_inv (n : ℕ) (c : Cut) (hc : c.Legal n) (x : ℕ) : c.tau (c.inv.tau x) = x := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have A := tau_cases c.inv x
  rw [inv_i, inv_j, inv_k] at A
  have B := tau_cases c (c.inv.tau x)
  generalize c.inv.tau x = y at A B ⊢
  generalize c.tau y = z at B ⊢
  omega

theorem tau_inv_pred (n : ℕ) (c : Cut) (hc : c.Legal n) (x : ℕ) (hx1 : 1 ≤ x)
    (hxi : x ≠ c.i) (hxj : x ≠ c.j) (hxk : x ≠ c.k) :
    c.tau (c.inv.tau x - 1) = x - 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have A := tau_cases c.inv x
  rw [inv_i, inv_j, inv_k] at A
  have B := tau_cases c (c.inv.tau x - 1)
  generalize c.inv.tau x = y at A B ⊢
  generalize c.tau (y - 1) = z at B ⊢
  omega

theorem inv_tau_range (n : ℕ) (c : Cut) (hc : c.Legal n) (x : ℕ) (hx1 : 1 ≤ x) (hxn : x ≤ n) :
    1 ≤ c.inv.tau x ∧ c.inv.tau x ≤ n := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have A := tau_cases c.inv x
  rw [inv_i, inv_j, inv_k] at A
  generalize c.inv.tau x = y at A ⊢
  omega

theorem adj_iff (n : ℕ) (p : ℕ → ℕ) (c : Cut) (hc : c.Legal n) (x : ℕ) (hx1 : 1 ≤ x)
    (hxi : x ≠ c.i) (hxj : x ≠ c.j) (hxk : x ≠ c.k) :
    (p x = p (x - 1) + 1) ↔
      (applyMove p c (c.inv.tau x) = applyMove p c (c.inv.tau x - 1) + 1) := by
  simp only [applyMove, Function.comp_apply]
  rw [tau_inv n c hc x, tau_inv_pred n c hc x hx1 hxi hxj hxk]

end Aux_BulteauTranspositions_NPHard_property_3

open BulteauTranspositions.NPHard Aux_BulteauTranspositions_NPHard_property_3 in
theorem solution (n : ℕ) (p : ℕ → ℕ) (hp : IsPermutation n p) (c : Cut) (hc : c.Legal n) :
    (∀ x ∈ Finset.Icc 1 n, x ≠ c.i → x ≠ c.j → x ≠ c.k →
      (adjacency p x ↔ adjacency (applyMove p c) (c.inv.tau x))) ∧
    breakpoints n p ≤ breakpoints n (applyMove p c) + 3 := by
  refine ⟨?_, ?_⟩
  · intro x hx hxi hxj hxk
    have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
    unfold adjacency
    exact adj_iff n p c hc x hx1 hxi hxj hxk
  · unfold breakpoints
    set S := (Finset.Icc 1 n).filter (fun x => p x ≠ p (x - 1) + 1) with hS
    set T := (Finset.Icc 1 n).filter
      (fun x => applyMove p c x ≠ applyMove p c (x - 1) + 1) with hT
    have h1 : S.card ≤ (S \ {c.i, c.j, c.k}).card + ({c.i, c.j, c.k} : Finset ℕ).card :=
      Finset.card_le_card_sdiff_add_card
    have h2 : ({c.i, c.j, c.k} : Finset ℕ).card ≤ 3 := Finset.card_le_three
    have h3 : (S \ {c.i, c.j, c.k}).card ≤ T.card := by
      refine Finset.card_le_card_of_injOn (fun x => c.inv.tau x) ?_ ?_
      · intro x hx
        have hx' : x ∈ S \ {c.i, c.j, c.k} := Finset.mem_coe.mp hx
        rw [Finset.mem_sdiff, hS, Finset.mem_filter, Finset.mem_Icc] at hx'
        obtain ⟨⟨⟨hx1, hxn⟩, hne⟩, hnot⟩ := hx'
        have hxi : x ≠ c.i := fun h => hnot (by simp [h])
        have hxj : x ≠ c.j := fun h => hnot (by simp [h])
        have hxk : x ≠ c.k := fun h => hnot (by simp [h])
        obtain ⟨r1, r2⟩ := inv_tau_range n c hc x hx1 hxn
        apply Finset.mem_coe.mpr
        rw [hT, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨r1, r2⟩, ?_⟩
        intro h
        exact hne ((adj_iff n p c hc x hx1 hxi hxj hxk).mpr h)
      · intro a _ b _ hab
        have ha := tau_inv n c hc a
        have hb := tau_inv n c hc b
        have hab' : c.inv.tau a = c.inv.tau b := hab
        calc a = c.tau (c.inv.tau a) := ha.symm
          _ = c.tau (c.inv.tau b) := by rw [hab']
          _ = b := hb
    omega
