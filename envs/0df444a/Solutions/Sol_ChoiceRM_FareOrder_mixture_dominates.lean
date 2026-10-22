-- Prove2me | solution 1 for ChoiceRM.FareOrder.mixture_dominates
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:15:47.466932+00:00
-- url     : https://prove2.me/submissions/a281f521-0893-47ea-9433-9f6985d2dd37

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_FareOrder_FareOrder
set_option autoImplicit false
open RevenueManagement ChoiceRM.FareOrder

theorem kk_abel (xs ds : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), xs j * ds j =
      xs m * ∑ j ∈ Finset.range (m + 1), ds j +
        ∑ i ∈ Finset.range m, (xs i - xs (i + 1)) * ∑ j ∈ Finset.range (i + 1), ds j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun i => (xs i - xs (i + 1)) * ∑ j ∈ Finset.range (i + 1), ds j) m,
      Finset.sum_range_succ ds (m + 1)]
    rw [Finset.sum_range_succ ds m]
    ring

theorem kk_nonneg_sum {n : ℕ} (x d : Fin n → ℝ) (hx : Antitone x)
    (hpre : ∀ i, i < n → 0 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i), d j)
    (htot : ∑ j, d j = 0) : 0 ≤ ∑ j, x j * d j := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set xs : ℕ → ℝ := fun i => if h : i < m + 1 then x ⟨i, h⟩ else 0 with hxs
  set ds : ℕ → ℝ := fun i => if h : i < m + 1 then d ⟨i, h⟩ else 0 with hds
  have hsum : ∑ j, x j * d j = ∑ j ∈ Finset.range (m + 1), xs j * ds j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => xs j * ds j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.1 j.isLt
    simp [hxs, hds, hj]
  have hpre' : ∀ i, i < m + 1 → 0 ≤ ∑ j ∈ Finset.range i, ds j := by
    intro i hi
    have h := hpre i hi
    have e1 : ∑ j ∈ Finset.range i, ds j =
        ∑ j ∈ Finset.range (m + 1), (if j < i then ds j else 0) := by
      rw [← Finset.sum_filter]
      congr 1
      ext j; simp only [Finset.mem_range, Finset.mem_filter]; omega
    have e2 := Fin.sum_univ_eq_sum_range (fun j => if j < i then ds j else 0) (m + 1)
    rw [e1, ← e2]
    rw [Finset.sum_filter] at h
    refine le_of_le_of_eq h (Finset.sum_congr rfl (fun j _ => ?_))
    have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.1 j.isLt
    simp [hds, hj]
  have htot' : ∑ j ∈ Finset.range (m + 1), ds j = 0 := by
    rw [← Fin.sum_univ_eq_sum_range ds (m + 1), ← htot]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.1 j.isLt
    simp [hds, hj]
  rw [hsum, kk_abel, htot', mul_zero, zero_add]
  refine Finset.sum_nonneg (fun i hi => ?_)
  have hi' : i < m := Finset.mem_range.1 hi
  refine mul_nonneg ?_ (hpre' (i + 1) (by omega))
  have : x ⟨i + 1, by omega⟩ ≤ x ⟨i, by omega⟩ := hx (by simp [Fin.le_def])
  simp only [hxs, show i < m + 1 by omega, show i + 1 < m + 1 by omega, dif_pos]
  linarith

theorem solution {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (hP : IsChoiceModel P) (hsupp : SupportedOn P) (T : Finset (Fin n))
    (α : Fin (n + 1) → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hα1 : ∑ k, α k = 1)
    (hpre : ∀ i, i < n → ∑ j ∈ complete n i, P T j ≤ ∑ j ∈ complete n i, mixProb P α j)
    (htot : ∑ j, mixProb P α j = ∑ j, P T j)
    (x : Fin n → ℝ) (hx : Antitone x) :
    fareValue P x T ≤ ∑ k : Fin (n + 1), α k * fareValue P x (complete n k.val) := by
  have hfv : ∀ S : Finset (Fin n), fareValue P x S = ∑ j, x j * P S j := by
    intro S
    unfold fareValue
    refine Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => ?_)
    rw [hsupp S j hj, mul_zero]
  have hmix : ∑ k : Fin (n + 1), α k * fareValue P x (complete n k.val) = ∑ j, x j * mixProb P α j := by
    simp_rw [hfv]
    unfold mixProb
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))
  rw [hmix, hfv T]
  have := kk_nonneg_sum x (fun j => mixProb P α j - P T j) hx
    (fun i hi => by
      have h := hpre i hi
      unfold complete at h
      simp only [Finset.sum_sub_distrib]
      linarith)
    (by simp only [Finset.sum_sub_distrib]; linarith)
  simp only [mul_sub, Finset.sum_sub_distrib] at this
  linarith
