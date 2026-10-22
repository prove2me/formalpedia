-- Prove2me | solution 1 for FlowsNetworks.Representatives.sum_of_permutation_matrices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:37:11.39841+00:00
-- url     : https://prove2.me/submissions/22a7564e-da89-41f1-ae8c-7f05f5d65926

import Mathlib
import Definitions.Def_FlowsNetworks_Representatives_SystemsOfRepresentatives
open FlowsNetworks.Representatives


theorem g69e_double_count {m n : ℕ} (S : Fin n → Finset (Fin m)) (X : Finset (Fin n)) :
    ∑ j ∈ X, (S j).card ≤ ∑ i ∈ X.biUnion S, (Finset.univ.filter (fun j => i ∈ S j)).card := by
  have h1 : ∀ j ∈ X, (S j).card = ∑ i ∈ X.biUnion S, if i ∈ S j then 1 else 0 := by
    intro j hj
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    ext i; simp only [Finset.mem_filter, Finset.mem_biUnion]
    exact ⟨fun h => ⟨⟨j, hj, h⟩, h⟩, fun h => h.2⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_boole, Nat.cast_id]
  apply Finset.card_le_card
  intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact fun h => h.2

theorem g69e_perm_gen {n : ℕ} (k : ℕ) : ∀ (A : Matrix (Fin n) (Fin n) ℕ),
    (∀ i j, A i j = 0 ∨ A i j = 1) →
    (∀ i, (Finset.univ.filter (fun j => A i j = 1)).card = k) →
    (∀ j, (Finset.univ.filter (fun i => A i j = 1)).card = k) →
    ∃ σ : Fin k → Equiv.Perm (Fin n), A = ∑ l, permMatrix (σ l) := by
  induction k with
  | zero =>
    intro A h01 hrow _
    refine ⟨fun l => l.elim0, ?_⟩
    ext i j
    have := hrow i
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at this
    have h := this (Finset.mem_univ j)
    rcases h01 i j with h' | h'
    · simp [h']
    · exact absurd h' h
  | succ k ih =>
    intro A h01 hrow hcol
    set t : Fin n → Finset (Fin n) := fun i => Finset.univ.filter (fun j => A i j = 1) with ht
    have hall : ∀ X : Finset (Fin n), X.card ≤ (X.biUnion t).card := by
      intro X
      have h := g69e_double_count t X
      have e1 : ∑ i ∈ X, (t i).card = X.card * (k + 1) := by
        simp [ht, hrow]
      have e2 : ∑ j ∈ X.biUnion t, (Finset.univ.filter (fun i => j ∈ t i)).card
          = (X.biUnion t).card * (k + 1) := by
        simp [ht, hcol]
      rw [e1, e2] at h
      exact Nat.le_of_mul_le_mul_right h (Nat.succ_pos k)
    obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
    have hfA : ∀ i, A i (f i) = 1 := fun i => by simpa [ht] using hft i
    set σ : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf) with hσ
    have hσA : ∀ i, A i (σ i) = 1 := fun i => hfA i
    set A' : Matrix (Fin n) (Fin n) ℕ := fun i j => A i j - permMatrix σ i j with hA'
    have hA'e : ∀ i j, A' i j = if σ i = j then 0 else A i j := by
      intro i j
      simp only [hA', permMatrix]
      split_ifs with h
      · subst h; rw [hσA]
      · simp
    have h01' : ∀ i j, A' i j = 0 ∨ A' i j = 1 := by
      intro i j; rw [hA'e]; split_ifs
      · exact Or.inl rfl
      · exact h01 i j
    have hrow' : ∀ i, (Finset.univ.filter (fun j => A' i j = 1)).card = k := by
      intro i
      have : Finset.univ.filter (fun j => A' i j = 1) =
          (Finset.univ.filter (fun j => A i j = 1)).erase (σ i) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hA'e]
        by_cases h : σ i = j
        · simp [h]
        · simp [h, Ne.symm h]
      rw [this, Finset.card_erase_of_mem (by simp [hσA]), hrow]; rfl
    have hcol' : ∀ j, (Finset.univ.filter (fun i => A' i j = 1)).card = k := by
      intro j
      have : Finset.univ.filter (fun i => A' i j = 1) =
          (Finset.univ.filter (fun i => A i j = 1)).erase (σ.symm j) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hA'e]
        have : σ i = j ↔ i = σ.symm j := (Equiv.eq_symm_apply σ).symm
        by_cases h : σ i = j
        · simp [h, this.1 h]
        · have h2 : ¬ i = σ.symm j := fun e => h (this.2 e)
          simp [h, h2]
      rw [this, Finset.card_erase_of_mem (by simpa using hσA (σ.symm j)), hcol]; rfl
    obtain ⟨τ, hτ⟩ := ih A' h01' hrow' hcol'
    refine ⟨Fin.cons σ τ, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hτ]
    ext i j
    simp only [Matrix.add_apply, hA'e, permMatrix]
    split_ifs with h
    · subst h; simp [hσA]
    · simp


/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Corollary 10.4 (p. 59). If `A` is an `n × n`
matrix whose entries are the integers `0` and `1`, with `k > 0` entries `1` in each row and in each
column, then `A` is a sum of `k` permutation matrices. -/
theorem solution {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) (hk : 0 < k)
    (hrow : ∀ i, (Finset.univ.filter (fun j => A i j = 1)).card = k)
    (hcol : ∀ j, (Finset.univ.filter (fun i => A i j = 1)).card = k) :
    ∃ σ : Fin k → Equiv.Perm (Fin n), A = ∑ l, permMatrix (σ l) := by
  exact g69e_perm_gen k A h01 hrow hcol

