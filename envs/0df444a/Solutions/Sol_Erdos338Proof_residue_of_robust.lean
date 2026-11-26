-- Prove2me | solution 1 for Erdos338Proof.residue_of_robust
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:28.250649+00:00
-- url     : https://prove2.me/submissions/7c50c8ee-d25a-4a64-a698-a1ae376ddd9b

module
public import Mathlib
public import Definitions.Def_Erdos338_Residue

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution (A : Set ℕ)
    (hrob : ∀ F : Set ℕ, F.Finite → ∃ h, ∀ᶠ m in Filter.atTop, ∃ S : Multiset ℕ,
      (∀ x ∈ S, x ∈ A \ F) ∧ Multiset.card S ≤ h ∧ S.sum = m)
    {Q : ℕ} (hQ : 0 < Q) (c : ℕ) :
    ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ ∑ x ∈ S, x ≡ c [MOD Q] := by
  classical
  set F : Set ℕ := {a | a ∈ A ∧ {x | x ∈ A ∧ x ≡ a [MOD Q]}.Finite} with hFdef
  have hF : F.Finite := by
    have hsub : F ⊆ ⋃ r ∈ Set.Iio Q,
        {x | x ∈ A ∧ x % Q = r ∧ {y | y ∈ A ∧ y % Q = r}.Finite} := by
      intro a ha
      simp only [Set.mem_iUnion, Set.mem_Iio]
      exact ⟨a % Q, Nat.mod_lt a hQ, ha.1, rfl, ha.2⟩
    refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iio Q) fun r _ ↦ ?_) hsub
    by_cases hr : {y | y ∈ A ∧ y % Q = r}.Finite
    · exact hr.subset fun x hx ↦ ⟨hx.1, hx.2.1⟩
    · exact Set.Finite.subset Set.finite_empty fun x hx ↦ (hr hx.2.2).elim
  obtain ⟨h, hh⟩ := hrob F hF
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hh
  obtain ⟨Ms, hMs, -, hsum⟩ := hN (c + Q * N) (by nlinarith)
  -- replace the summands by distinct elements of the same classes
  have key : ∀ Ms : Multiset ℕ, (∀ x ∈ Ms, x ∈ A \ F) →
      ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ ∑ x ∈ S, x ≡ Ms.sum [MOD Q] := by
    intro Ms
    induction Ms using Multiset.induction_on with
    | empty => exact fun _ ↦ ⟨∅, by simp, by simp [Nat.ModEq.refl]⟩
    | cons a Ms ih =>
      intro hMs
      obtain ⟨S, hSA, hSsum⟩ := ih fun x hx ↦ hMs x (Multiset.mem_cons_of_mem hx)
      have ha := hMs a (Multiset.mem_cons_self a Ms)
      have hinf : {x | x ∈ A ∧ x ≡ a [MOD Q]}.Infinite := fun hfin ↦ ha.2 ⟨ha.1, hfin⟩
      obtain ⟨a', ⟨ha'A, ha'a⟩, ha'S⟩ := hinf.exists_notMem_finset S
      refine ⟨insert a' S, fun x hx ↦ ?_, ?_⟩
      · rcases mem_insert.1 hx with rfl | hx
        exacts [ha'A, hSA x hx]
      · rw [sum_insert ha'S, Multiset.sum_cons]
        exact ha'a.add hSsum
  obtain ⟨S, hSA, hS⟩ := key Ms hMs
  refine ⟨S, hSA, hS.trans ?_⟩
  rw [hsum]
  show (c + Q * N) % Q = c % Q
  exact Nat.add_mul_mod_self_left c Q N
end Erdos338Proof
