-- Prove2me | solution 1 for BondySimonovits.exists_large_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:04:14.430281+00:00
-- url     : https://prove2.me/submissions/c72363c8-3c2a-4e8f-a2f2-39e3b1f52388

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSBasic

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [Fintype V]
namespace BondySimonovits
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ f : V → Bool, ∑ v, (univ.filter (G.Adj v)).card ≤
      2 * ∑ v, (univ.filter (fun u => G.Adj v u ∧ f v ≠ f u)).card := by
  classical
  set Φ : (V → Bool) → ℕ := fun f => ∑ v, (univ.filter (fun u => G.Adj v u ∧ f v ≠ f u)).card
  obtain ⟨f, -, hf⟩ := Finset.exists_max_image (univ : Finset (V → Bool)) Φ univ_nonempty
  refine ⟨f, ?_⟩
  have local_opt : ∀ v, (univ.filter (fun u => G.Adj v u ∧ f v = f u)).card ≤
      (univ.filter (fun u => G.Adj v u ∧ f v ≠ f u)).card := by
    intro v
    by_contra hcon
    push Not at hcon
    set f' := Function.update f v (!f v)
    have hf' := hf f' (mem_univ _)
    set same : ℕ := (univ.filter (fun u => G.Adj v u ∧ f v = f u)).card
    set cut : ℕ := (univ.filter (fun u => G.Adj v u ∧ f v ≠ f u)).card
    have key : ∀ a b, ((if G.Adj a b ∧ f' a ≠ f' b then 1 else 0 : ℤ) -
        (if G.Adj a b ∧ f a ≠ f b then 1 else 0 : ℤ)) =
        (if a = v then ((if G.Adj v b ∧ f v = f b then 1 else 0 : ℤ) -
          (if G.Adj v b ∧ f v ≠ f b then 1 else 0 : ℤ)) else 0) +
        (if b = v then ((if G.Adj v a ∧ f v = f a then 1 else 0 : ℤ) -
          (if G.Adj v a ∧ f v ≠ f a then 1 else 0 : ℤ)) else 0) := by
      intro a b
      by_cases ha : a = v <;> by_cases hb : b = v
      · subst ha hb; simp
      · subst ha
        simp [f', hb]
      · subst hb
        by_cases hab : f a = f b
        · simp [f', ha, G.adj_comm, hab]
        · have hba : ¬ f b = f a := fun h => hab h.symm
          simp [f', ha, G.adj_comm, hab, hba]
      · simp [f', ha, hb]
    have hcard : ∀ g : V → Bool, (Φ g : ℤ) =
        ∑ a, ∑ b, (if G.Adj a b ∧ g a ≠ g b then 1 else 0 : ℤ) := by
      intro g; simp only [Φ, Nat.cast_sum, Finset.card_filter, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero]
    have hsame : (same : ℤ) = ∑ b, (if G.Adj v b ∧ f v = f b then 1 else 0 : ℤ) := by
      simp only [same, Nat.cast_sum, Finset.card_filter, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero]
    have hcut : (cut : ℤ) = ∑ b, (if G.Adj v b ∧ f v ≠ f b then 1 else 0 : ℤ) := by
      simp only [cut, Nat.cast_sum, Finset.card_filter, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero]
    have hΦ : (Φ f' : ℤ) - Φ f = 2 * ((same : ℤ) - cut) := by
      rw [hcard, hcard, ← Finset.sum_sub_distrib]
      simp_rw [← Finset.sum_sub_distrib, key, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Finset.sum_sub_distrib, hsame, hcut]
      rw [Finset.sum_eq_single v (fun b _ hb => by simp [hb]) (by simp)]
      simp only [ite_true, Finset.sum_sub_distrib]
      ring
    omega
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  have hsplit : (univ.filter (G.Adj v)).card =
      (univ.filter (fun u => G.Adj v u ∧ f v = f u)).card +
      (univ.filter (fun u => G.Adj v u ∧ f v ≠ f u)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      tauto
    · rw [Finset.disjoint_filter]
      intro u _ h1 h2
      exact h2.2 h1.2
  have := local_opt v
  omega
end BondySimonovits
