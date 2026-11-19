-- Prove2me | solution 1 for Erdos195.zero_one_fifteen_mod4_three_extension
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T19:50:09.058824+00:00
-- url     : https://prove2.me/submissions/c6990cdb-832a-4391-bfcc-84230f3a05b6

import Definitions.Def_Erdos195_tree
import Theorems.Thm_Erdos195_exists_treeLt_safe_iff
import Theorems.Thm_Erdos195_specified_first_safe_order
import Theorems.Thm_Erdos195_safe_word_composition
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Erdos195

private def θfalse : ℕ → ℤ → Bool := fun _ _ => false

private lemma instPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private lemma treeLt_false {x y : ℤ} (hne : x ≠ y)
    (hbit : ¬ bitOne x (padicValInt 2 (y - x))) :
    treeLt θfalse x y := by
  refine ⟨hne, ?_⟩
  simp [θfalse, hbit]

private lemma exists_safe_nil : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) ([] : List ℤ) := by
  refine (exists_treeLt_safe_iff ([] : List ℤ)).mpr ⟨?_, ?_⟩
  · intro a b ha; cases ha
  · intro a b a' b' ha; cases ha

private lemma exists_safe_singleton (a : ℤ) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [a] := by
  refine (exists_treeLt_safe_iff ([a] : List ℤ)).mpr ⟨?_, ?_⟩
  · intro x y hx hy _ hord1 _
    have hx' : x = a := by simpa using hx
    have hy' : y = a := by simpa using hy
    subst hx'; subst hy'
    exact (lt_irrefl _ hord1).elim
  · intro x y x' y' hx hy hord _ _ _ _ _ _ _ _ _
    have hx0 : x = a := by simpa using hx
    have hy0 : y = a := by simpa using hy
    subst hx0; subst hy0
    exact (lt_irrefl _ hord).elim

private lemma residues_0213_perm :
    ([0, 2, 1, 3] : List ℤ).Perm ((List.range (2 ^ 2)).map (fun n : ℕ => (n : ℤ))) := by
  decide

private lemma residues_0213_tree_order :
    ∃ θ0 : ℕ → ℤ → Bool, ([0, 2, 1, 3] : List ℤ).Pairwise (treeLt θ0) := by
  haveI := instPrimeTwo
  refine ⟨θfalse, ?_⟩
  have h02 : treeLt θfalse 0 2 := by
    have hpv : padicValInt 2 ((2 : ℤ) - 0) = 1 := padicValInt.self (by decide : 1 < 2)
    refine treeLt_false (by decide) ?_
    rw [hpv]; simp [bitOne]
  have h01 : treeLt θfalse 0 1 := by
    have hpv : padicValInt 2 ((1 : ℤ) - 0) = 0 := by simp
    refine treeLt_false (by decide) ?_
    rw [hpv]; simp [bitOne]
  have h03 : treeLt θfalse 0 3 := by
    have : ¬ (2 : ℤ) ∣ (3 : ℤ) := by decide
    have hpv : padicValInt 2 ((3 : ℤ) - 0) = 0 := padicValInt.eq_zero_of_not_dvd this
    refine treeLt_false (by decide) ?_
    rw [hpv]; simp [bitOne]
  have h21 : treeLt θfalse 2 1 := by
    have : ¬ (2 : ℤ) ∣ ((1 : ℤ) - 2) := by decide
    have hpv : padicValInt 2 ((1 : ℤ) - 2) = 0 := padicValInt.eq_zero_of_not_dvd this
    refine treeLt_false (by decide) ?_
    rw [hpv]; simp [bitOne]
  have h23 : treeLt θfalse 2 3 := by
    have hpv : padicValInt 2 ((3 : ℤ) - 2) = 0 := by simp
    refine treeLt_false (by decide) ?_
    rw [hpv]; simp [bitOne]
  have h13 : treeLt θfalse 1 3 := by
    have hpv : padicValInt 2 ((3 : ℤ) - 1) = 1 := padicValInt.self (by decide : 1 < 2)
    refine treeLt_false (by decide) ?_
    rw [hpv]; simp [bitOne]
  simp [List.pairwise_cons, h02, h01, h03, h21, h23, h13]

private lemma recover_mod4 {z : ℤ} (hz : z % 4 = 3) : 3 + 4 * ((z - 3) / 4) = z := by
  have hsplit : (z - 3) % 4 + (z - 3) / 4 * 4 = z - 3 := Int.emod_add_ediv_mul (z - 3) 4
  have hmod : (z - 3) % 4 = 0 := by omega
  omega

private lemma lift4_inj {x y : ℤ} (h : 3 + 4 * x = 3 + 4 * y) : x = y := by omega

private lemma lift4_mod (x : ℤ) : (3 + 4 * x) % 4 = 3 := by omega

private lemma compose_blocks (A : List ℤ) :
    (([0, 2, 1, 3] : List ℤ).map
        (fun s =>
          ((if s = 0 then [0] else if s = 1 then [0] else if s = 3 then A else []) : List ℤ).map
            (fun x => s + (2 : ℤ) ^ 2 * x))).flatten
      = 0 :: 1 :: A.map (fun t => 3 + 4 * t) := by
  have hpow : (2 : ℤ) ^ 2 = 4 := by decide
  simp [hpow, List.flatten]

theorem zero_one_fifteen_mod4_three_extension (F : Finset ℤ)
    (hF : ∀ z ∈ F, z % 4 = 3) :
    ∃ Q : List ℤ, Q.Nodup ∧ (∃ T : List ℤ, Q = 0 :: 1 :: 15 :: T) ∧ (∀ z ∈ F, z ∈ Q) ∧
      ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q := by
  classical
  let H : Finset ℤ := insert 3 (F.image fun z => (z - 3) / 4)
  have h3H : (3 : ℤ) ∈ H := Finset.mem_insert_self _ _
  obtain ⟨A, hndA, hmemA, hheadA, hsafeA⟩ := specified_first_safe_order H 3 h3H
  let residues : List ℤ := [0, 2, 1, 3]
  let Afun : ℤ → List ℤ := fun s =>
    if s = 0 then [0] else if s = 1 then [0] else if s = 3 then A else []
  let Q : List ℤ := 0 :: 1 :: A.map (fun t => 3 + 4 * t)
  have hQeq : Q = (residues.map (fun s => (Afun s).map (fun x => s + (2 : ℤ) ^ 2 * x))).flatten := by
    simpa [Q, residues, Afun] using (compose_blocks A).symm
  have hAs : ∀ s : ℤ, 0 ≤ s → s < (2 : ℤ) ^ 2 →
      ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (Afun s) := by
    intro s hs0 hs1
    have hsrange : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by
      have : s < 4 := by
        have : (2 : ℤ) ^ 2 = 4 := by decide
        rwa [this] at hs1
      omega
    rcases hsrange with rfl | rfl | rfl | rfl
    · simpa [Afun] using exists_safe_singleton (0 : ℤ)
    · simpa [Afun] using exists_safe_singleton (0 : ℤ)
    · simpa [Afun] using exists_safe_nil
    · simpa [Afun] using hsafeA
  have hsafeQ : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q :=
    (safe_word_composition 2 (by decide) Afun residues residues_0213_perm
      residues_0213_tree_order Q hQeq).mpr hAs
  have hnd : Q.Nodup := by
    refine (List.nodup_cons).2 ⟨?_, (List.nodup_cons).2 ⟨?_, ?_⟩⟩
    · intro h
      have : (0 : ℤ) = 1 ∨ ∃ t ∈ A, 3 + 4 * t = 0 := by
        simpa [List.mem_cons, List.mem_map] using h
      rcases this with h01 | ⟨t, _, ht⟩
      · cases h01
      · have : (0 : ℤ) % 4 = 3 := by
          rw [← ht]
          exact lift4_mod t
        omega
    · intro h
      obtain ⟨t, _, ht⟩ := List.mem_map.mp h
      have : (1 : ℤ) % 4 = 3 := by
        rw [← ht]
        exact lift4_mod t
      omega
    · exact hndA.map (fun {x y} h => lift4_inj h)
  have hpref : ∃ T : List ℤ, Q = 0 :: 1 :: 15 :: T := by
    cases A with
    | nil =>
      cases hheadA
    | cons a t =>
      have ha : a = 3 := by
        simpa [List.head?] using hheadA
      subst ha
      refine ⟨t.map (fun u => 3 + 4 * u), ?_⟩
      simp [Q]
  have hFmem : ∀ z ∈ F, z ∈ Q := by
    intro z hz
    have hz3 := hF z hz
    have hxH : (z - 3) / 4 ∈ H :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    have hxA : (z - 3) / 4 ∈ A := (hmemA _).2 hxH
    exact List.mem_cons_of_mem _ <|
      List.mem_cons_of_mem _ <|
        List.mem_map.mpr ⟨(z - 3) / 4, hxA, recover_mod4 hz3⟩
  exact ⟨Q, hnd, hpref, hFmem, hsafeQ⟩

end Erdos195

theorem solution (F : Finset ℤ) (hF : ∀ z ∈ F, z % 4 = 3) :
    ∃ Q : List ℤ, Q.Nodup ∧ (∃ T : List ℤ, Q = 0 :: 1 :: 15 :: T) ∧ (∀ z ∈ F, z ∈ Q) ∧
      ∃ θ : ℕ → ℤ → Bool, Erdos195.Safe (Erdos195.treeLt θ) Q :=
  Erdos195.zero_one_fifteen_mod4_three_extension F hF
