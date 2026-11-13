-- Prove2me | solution 1 for DirKECC1549.Main.hitting_set_stabilizes
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-13T03:59:50.560546+00:00
-- url     : https://prove2.me/submissions/28061ddb-fa90-4d4e-9ce3-3c2ad352a105

import Definitions.Def_DirKECC1549_Main_HittingSet
set_option autoImplicit false
open Finset DirKECC1549.Main

private theorem parent_bound {n : ℕ} (r : Fin n) (par : Fin n → Fin n)
    (hreach : ∀ v, ∃ j : ℕ, par^[j] v = r) (v : Fin n) :
    ∃ j < n, par^[j] v = r := by
  classical
  let d := Nat.find (hreach v)
  have hd : par^[d] v = r := Nat.find_spec (hreach v)
  have hminimal : ∀ j < d, par^[j] v ≠ r := by
    intro j hj
    exact Nat.find_min (hreach v) hj
  have hcollision (i j : ℕ) (hij : i < j) (hj : j ≤ d)
      (he : par^[i] v = par^[j] v) : False := by
    have hl : d - j + i < d := by omega
    apply hminimal (d - j + i) hl
    rw [Function.iterate_add_apply, he, ← Function.iterate_add_apply]
    have : d - j + j = d := by omega
    rw [this]
    exact hd
  have hinj : Function.Injective (fun i : Fin (d + 1) ↦ par^[i.val] v) := by
    intro i j h
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · exact False.elim (hcollision i.val j.val hij (by omega) h)
    · exact Fin.ext hij
    · exact False.elim (hcollision j.val i.val hij (by omega) h.symm)
  have hcard := Fintype.card_le_of_injective (fun i : Fin (d + 1) ↦ par^[i.val] v) hinj
  simp only [Fintype.card_fin] at hcard
  exact ⟨d, by omega, hd⟩

private theorem change_chain {n : ℕ} (r : Fin n) (par : Fin n → Fin n)
    (deg : Fin n → ℕ) (b : ℕ) (t : ℕ) (v : Fin n)
    (h : alg2Rho r par deg b (t + 1) v ≠ alg2Rho r par deg b t v) :
    ∃ u : Fin n, par^[t] u = v ∧ ∀ i < t, par^[i] u ≠ r := by
  classical
  induction t generalizing v with
  | zero => exact ⟨v, rfl, by simp⟩
  | succ t ih =>
    have hc : ∃ u ∈ treeChildren r par v,
        alg2Rho r par deg b (t + 1) u ≠ alg2Rho r par deg b t u := by
      by_contra hn
      push Not at hn
      have hs : (∑ u ∈ treeChildren r par v, alg2Rho r par deg b (t + 1) u) =
          ∑ u ∈ treeChildren r par v, alg2Rho r par deg b t u := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hn u hu
      apply h
      change (if b < deg v + ∑ u ∈ treeChildren r par v, alg2Rho r par deg b (t + 1) u
        then 0 else deg v + ∑ u ∈ treeChildren r par v, alg2Rho r par deg b (t + 1) u) =
        (if b < deg v + ∑ u ∈ treeChildren r par v, alg2Rho r par deg b t u
        then 0 else deg v + ∑ u ∈ treeChildren r par v, alg2Rho r par deg b t u)
      rw [hs]
    obtain ⟨u, hu, hune⟩ := hc
    obtain ⟨w, hw, hpath⟩ := ih u hune
    refine ⟨w, ?_, ?_⟩
    · rw [Function.iterate_succ_apply', hw]
      exact (Finset.mem_filter.mp hu).2.2
    · intro i hi
      by_cases hit : i < t
      · exact hpath i hit
      · have hi' : i = t := by omega
        subst i
        rw [hw]
        exact (Finset.mem_filter.mp hu).2.1

theorem solution {n : ℕ} (r : Fin n) (par : Fin n → Fin n)
    (deg : Fin n → ℕ) (b : ℕ) (hroot : par r = r)
    (hreach : ∀ v, ∃ j : ℕ, par^[j] v = r) (v : Fin n) :
    alg2Rho r par deg b (n + 1) v = alg2Rho r par deg b n v := by
  classical
  by_contra h
  obtain ⟨w, _, hpath⟩ := change_chain r par deg b n v h
  obtain ⟨j, hj, heq⟩ := parent_bound r par hreach w
  exact hpath j hj heq
