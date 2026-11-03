-- Prove2me | solution 1 for BlottoLP.Flow.best_response_dp
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:05:05.106597+00:00
-- url     : https://prove2.me/submissions/74e7c14c-fdd7-42fc-ad1b-2ebddc530419

import Mathlib
import Definitions.Def_BlottoLP_Flow_Model

namespace BlottoLP.Flow.BRDPAux

open Finset BlottoLP.Flow

/-- Splitting off the last summand of a prefix sum over `Fin K`. -/
theorem sum_lt_succ {K : ℕ} (f : Fin K → ℝ) (k : ℕ) (hk : k < K) :
    ∑ k' ∈ univ.filter (fun k' : Fin K => (k' : ℕ) < k + 1), f k' =
      ∑ k' ∈ univ.filter (fun k' : Fin K => (k' : ℕ) < k), f k' + f ⟨k, hk⟩ := by
  have : univ.filter (fun k' : Fin K => (k' : ℕ) < k + 1) =
      insert ⟨k, hk⟩ (univ.filter (fun k' : Fin K => (k' : ℕ) < k)) := by
    ext k'
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  rw [this, sum_insert (by simp), add_comm]

theorem sum_lt_succ_nat {K : ℕ} (f : Fin K → ℕ) (k : ℕ) (hk : k < K) :
    ∑ k' ∈ univ.filter (fun k' : Fin K => (k' : ℕ) < k + 1), f k' =
      ∑ k' ∈ univ.filter (fun k' : Fin K => (k' : ℕ) < k), f k' + f ⟨k, hk⟩ := by
  have : univ.filter (fun k' : Fin K => (k' : ℕ) < k + 1) =
      insert ⟨k, hk⟩ (univ.filter (fun k' : Fin K => (k' : ℕ) < k)) := by
    ext k'
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  rw [this, sum_insert (by simp), add_comm]

section
variable {K N : ℕ} (W : Fin K → Fin (N + 1) → ℝ) (C : ℝ)

/-- Weights extended by `0` beyond the last battlefield. -/
def W' (k : ℕ) (t : Fin (N + 1)) : ℝ := if h : k < K then W ⟨k, h⟩ t else 0

theorem nonempty_le {N : ℕ} (i : Fin (N + 1)) :
    (univ.filter (fun j : Fin (N + 1) => j ≤ i)).Nonempty :=
  ⟨0, mem_filter.2 ⟨mem_univ _, Fin.zero_le _⟩⟩

def subF {N : ℕ} (i j : Fin (N + 1)) : Fin (N + 1) :=
  ⟨(i : ℕ) - j, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- The dynamic program: `Dn k i` is the maximum weight of a path from `v_{0,0}` to `v_{k,i}`
(with value `-C` at the unreachable vertices `v_{0,i}`, `i > 0`). -/
def Dn : ℕ → Fin (N + 1) → ℝ
  | 0 => fun i => if i = 0 then 0 else -C
  | k + 1 => fun i => (univ.filter (fun j : Fin (N + 1) => j ≤ i)).sup'
      (nonempty_le i) (fun j => Dn k j + W' W k (subF i j))

theorem Dn_ge (k : ℕ) (i j : Fin (N + 1)) (hji : j ≤ i) :
    Dn W C k j + W' W k (subF i j) ≤ Dn W C (k + 1) i := by
  show _ ≤ (univ.filter (fun j : Fin (N + 1) => j ≤ i)).sup' (nonempty_le i) _
  exact le_sup' (fun j => Dn W C k j + W' W k (subF i j)) (mem_filter.2 ⟨mem_univ j, hji⟩ : j ∈ univ.filter (fun j' : Fin (N + 1) => j' ≤ i))

/-- Invariant: every DP value is dominated by the weight of a partial allocation reaching it,
except at the unreachable vertices of layer `0`. -/
theorem Dn_witness (S : ℝ) (hS : ∀ k t, |W' W k t| ≤ S) (hC : 2 * S ≤ C) :
    ∀ k : ℕ, k ≤ K → ∀ i : Fin (N + 1), (k = 0 ∧ i ≠ 0) ∨
      ∃ z : Fin k → Fin (N + 1), ∑ k', (z k' : ℕ) = i ∧
        Dn W C k i ≤ ∑ k' : Fin k, W' W k' (z k') := by
  intro k
  induction k with
  | zero =>
    intro _ i
    by_cases hi : i = 0
    · right; refine ⟨Fin.elim0, by simp [hi], by simp [Dn, hi]⟩
    · left; exact ⟨rfl, hi⟩
  | succ k ih =>
    intro hk i
    right
    obtain ⟨j, hj, hjmax⟩ := exists_mem_eq_sup' (s := univ.filter (fun j : Fin (N + 1) => j ≤ i))
      (nonempty_le i) (fun j => Dn W C k j + W' W k (subF i j))
    have hD : Dn W C (k + 1) i = Dn W C k j + W' W k (subF i j) := hjmax
    simp only [mem_filter, mem_univ, true_and] at hj
    rcases ih (by omega) j with ⟨rfl, hj0⟩ | ⟨z, hz, hzD⟩
    · -- start at layer 0 off the source: dominated by putting all `i` troops on battlefield 0
      refine ⟨fun _ => i, by simp, ?_⟩
      rw [hD]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero]
      have h1 : Dn W C 0 j = -C := by simp [Dn, hj0]
      rw [h1]
      have a1 := hS 0 (subF i j)
      have a2 := hS 0 i
      rw [abs_le] at a1 a2
      linarith
    · refine ⟨Fin.snoc z (subF i j), ?_, ?_⟩
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, subF]
        rw [hz]; rw [Fin.le_def] at hj; omega
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
        rw [hD]; linarith
end

end BlottoLP.Flow.BRDPAux

open BlottoLP.Flow BlottoLP.Flow.BRDPAux Finset in
theorem solution (K N : ℕ) (W : Fin K → Fin (N + 1) → ℝ) (t : ℝ) :
    (∀ y : Pure K N, ∑ k, W k (y.1 k) ≤ t) ↔
      ∃ D : Fin (K + 1) → Fin (N + 1) → ℝ, IsDPBound W D ∧ D (Fin.last K) (Fin.last N) ≤ t := by
  classical
  constructor
  · intro hy
    set S : ℝ := ∑ k : Fin K, ∑ s : Fin (N + 1), |W k s| with hSdef
    have hS : ∀ k t', |W' W k t'| ≤ S := by
      intro k t'
      unfold W'
      split_ifs with h
      · calc |W ⟨k, h⟩ t'| ≤ ∑ s : Fin (N + 1), |W ⟨k, h⟩ s| :=
              single_le_sum (f := fun s => |W ⟨k, h⟩ s|) (fun _ _ => abs_nonneg _) (mem_univ t')
          _ ≤ S := single_le_sum (f := fun k => ∑ s : Fin (N + 1), |W k s|)
              (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ _)
      · simp only [abs_zero]; exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
    set C : ℝ := 2 * S + |t| with hC
    refine ⟨fun k i => Dn W C k i, ⟨by simp [Dn], ?_⟩, ?_⟩
    · intro k i j s hjs
      have hji : j ≤ i := by rw [Fin.le_def]; omega
      have := Dn_ge W C k i j hji
      have hsub : subF i j = s := by ext; simp [subF]; omega
      have hW : W' W k s = W k s := by simp [W', k.isLt]
      simp only [Fin.coe_castSucc, Fin.val_succ]
      rw [hsub, hW] at this
      exact this
    · simp only [Fin.val_last]
      rcases Dn_witness W C S hS (by rw [hC]; linarith [abs_nonneg t]) K le_rfl (Fin.last N)
        with ⟨hK0, hN0⟩ | ⟨z, hz, hzD⟩
      · subst hK0
        have : Dn W C 0 (Fin.last N) = -C := by simp [Dn, hN0]
        rw [this, hC]
        have : 0 ≤ S := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
        linarith [neg_abs_le t]
      · have hy' := hy ⟨z, by rw [hz]; simp⟩
        refine hzD.trans (le_of_eq_of_le ?_ hy')
        refine sum_congr rfl fun k _ => ?_
        simp [W', k.isLt]
  · rintro ⟨D, ⟨hD0, hD⟩, hDt⟩ y
    -- prefix invariant
    have key : ∀ k : ℕ, (hk : k ≤ K) →
        ∑ k' ∈ univ.filter (fun k' : Fin K => (k' : ℕ) < k), W k' (y.1 k') ≤
          D ⟨k, Nat.lt_succ_of_le hk⟩ ((prefixPath y).1 ⟨k, Nat.lt_succ_of_le hk⟩) := by
      intro k
      induction k with
      | zero =>
        intro hk
        have h0 : (prefixPath y).1 ⟨0, Nat.lt_succ_of_le hk⟩ = 0 := (prefixPath y).2.1
        rw [h0]
        rw [show (⟨0, _⟩ : Fin (K + 1)) = 0 from rfl, hD0]
        simp
      | succ k ih =>
        intro hk
        have hkK : k < K := hk
        rw [sum_lt_succ (fun k' => W k' (y.1 k')) k hkK]
        have h1 := ih (by omega)
        have h2 := hD ⟨k, hkK⟩ ((prefixPath y).1 ⟨k + 1, Nat.lt_succ_of_le hk⟩)
          ((prefixPath y).1 ⟨k, Nat.lt_succ_of_le (by omega)⟩) (y.1 ⟨k, hkK⟩) (by
            simp only [prefixPath, prefixSum]
            rw [sum_lt_succ_nat (fun k' => (y.1 k' : ℕ)) k hkK])
        have e1 : (⟨k, hkK⟩ : Fin K).castSucc = ⟨k, Nat.lt_succ_of_le (by omega)⟩ := rfl
        have e2 : (⟨k, hkK⟩ : Fin K).succ = ⟨k + 1, Nat.lt_succ_of_le hk⟩ := rfl
        rw [e1, e2] at h2
        linarith
    have := key K le_rfl
    have hlast : (prefixPath y).1 ⟨K, Nat.lt_succ_self K⟩ = Fin.last N := (prefixPath y).2.2.1
    rw [hlast] at this
    have hall : univ.filter (fun k' : Fin K => (k' : ℕ) < K) = univ := by
      ext k'; simp [k'.isLt]
    rw [hall] at this
    exact this.trans (le_of_eq_of_le rfl hDt)
