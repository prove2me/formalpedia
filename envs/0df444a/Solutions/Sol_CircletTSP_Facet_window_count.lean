-- Prove2me | solution 1 for CircletTSP.Facet.window_count
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:22:37.095973+00:00
-- url     : https://prove2.me/submissions/79f57aea-ec5d-421c-b211-67a7bdbcd77a

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

set_option autoImplicit false
open scoped BigOperators
open Fin.NatCast

namespace CircletTSP.Facet.WindowCountProof

lemma shift_eq_add {n : ℕ} [NeZero n] (u : Fin n) (k : ℕ) :
    shift u k = u + (k : Fin n) := by
  apply Fin.ext
  simp [shift, Fin.val_add, Nat.add_mod]

lemma shift_shift {n : ℕ} (u : Fin n) (a b : ℕ) :
    shift (shift u a) b = shift u (a + b) := by
  apply Fin.ext
  change ((u.val + a) % n + b) % n = (u.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

lemma shift_zero {n : ℕ} (u : Fin n) : shift u 0 = u := by
  apply Fin.ext
  simp [shift, Nat.mod_eq_of_lt u.isLt]

lemma shift_add_n {n : ℕ} (u : Fin n) (k : ℕ) : shift u (k + n) = shift u k := by
  apply Fin.ext
  simp [shift, Nat.add_mod]

lemma shift_injective {n : ℕ} (hn : 0 < n) (k : ℕ) :
    Function.Injective (fun u : Fin n => shift u k) := by
  have : NeZero n := ⟨hn.ne'⟩
  intro u v h
  simp only [shift_eq_add] at h
  exact add_right_cancel h

lemma sum_shift {n : ℕ} (hn : 0 < n) (k : ℕ) (f : Fin n → ℝ) :
    (∑ u : Fin n, f (shift u k)) = ∑ u : Fin n, f u := by
  have : NeZero n := ⟨hn.ne'⟩
  simp only [shift_eq_add]
  exact Equiv.sum_comp (Equiv.addRight (k : Fin n)) f

lemma cycLen_symm {n : ℕ} (u v : Fin n) : cycLen n u v = cycLen n v u := by
  have h := Int.natAbs_neg ((u.val : ℤ) - v.val)
  rw [neg_sub] at h
  simp only [cycLen, h]

lemma twice_upper_sum {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hsym : ∀ u v, f u v = f v u) (hdiag : ∀ u, f u u = 0) :
    2 * (∑ u : Fin n, ∑ v : Fin n, if u < v then f u v else 0) =
      ∑ u : Fin n, ∑ v : Fin n, f u v := by
  have hp (u v : Fin n) : f u v =
      (if u < v then f u v else 0) + (if v < u then f v u else 0) := by
    rcases lt_trichotomy u v with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · subst v
      simp [hdiag]
    · simp [h, not_lt_of_ge h.le, hsym]
  have hswap : (∑ u : Fin n, ∑ v : Fin n, if v < u then f v u else 0) =
      ∑ u : Fin n, ∑ v : Fin n, if u < v then f u v else 0 := by
    rw [Finset.sum_comm]
  have hsum : (∑ u : Fin n, ∑ v : Fin n, f u v) =
      (∑ u : Fin n, ∑ v : Fin n, if u < v then f u v else 0) +
      (∑ u : Fin n, ∑ v : Fin n, if v < u then f v u else 0) := by
    calc
      _ = ∑ u : Fin n, ∑ v : Fin n,
          ((if u < v then f u v else 0) + (if v < u then f v u else 0)) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        exact hp u v
      _ = _ := by simp only [Finset.sum_add_distrib]
  rw [hswap] at hsum
  linarith

lemma twice_lenCount {n : ℕ} (i : ℕ) (hi : i ≠ 0) (x : Fin n → Fin n → ℝ)
    (hsym : ∀ u v, x u v = x v u) :
    2 * lenCount n i x =
      ∑ u : Fin n, ∑ v : Fin n, if cycLen n u v = i then x u v else 0 := by
  have h := twice_upper_sum (fun u v => if cycLen n u v = i then x u v else 0)
    (by intro u v; rw [cycLen_symm u v, hsym u v])
    (by intro u; simp [cycLen, Ne.symm hi])
  simpa only [lenCount, ite_and] using h

lemma shift_one_val {n : ℕ} (u : Fin n) :
    (shift u 1).val = if u.val + 1 < n then u.val + 1 else 0 := by
  change (u.val + 1) % n = _
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have h' : u.val + 1 = n := by omega
    simp [h']

lemma cycLen_one_iff {n : ℕ} (hn : 2 < n) (u v : Fin n) :
    cycLen n u v = 1 ↔ v = shift u 1 ∨ u = shift v 1 := by
  simp only [Fin.ext_iff, shift_one_val]
  unfold cycLen
  by_cases h : u.val ≤ v.val
  · rw [Int.natAbs_natCast_sub_natCast_of_le h]
    split_ifs <;> omega
  · rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega : v.val ≤ u.val)]
    split_ifs <;> omega

lemma shift_two_ne_self {n : ℕ} (hn : 2 < n) (u : Fin n) : shift u 2 ≠ u := by
  have : NeZero n := ⟨by omega⟩
  intro h
  rw [shift_eq_add] at h
  have hz : (2 : Fin n) = 0 := add_left_cancel (h.trans (add_zero u).symm)
  have hv := congrArg Fin.val hz
  norm_num [Nat.mod_eq_of_lt hn] at hv

lemma short_directions_disjoint {n : ℕ} (hn : 2 < n) (u v : Fin n) :
    ¬ (v = shift u 1 ∧ u = shift v 1) := by
  rintro ⟨rfl, h⟩
  exact shift_two_ne_self hn u (by simpa only [shift_shift] using h.symm)

lemma shift_half_val {n : ℕ} (hn : 0 < n) (heven : 2 ∣ n) (u : Fin n) :
    (shift u (n / 2)).val =
      if u.val < n / 2 then u.val + n / 2 else u.val - n / 2 := by
  have heq : n / 2 + n / 2 = n := by omega
  change (u.val + n / 2) % n = _
  split_ifs with hu
  · apply Nat.mod_eq_of_lt
    omega
  · have hh : u.val + n / 2 = (u.val - n / 2) + n := by omega
    rw [hh, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma cycLen_half_iff {n : ℕ} (hn : 0 < n) (heven : 2 ∣ n) (u v : Fin n) :
    cycLen n u v = n / 2 ↔ v = shift u (n / 2) := by
  have heq : n / 2 + n / 2 = n := by omega
  simp only [Fin.ext_iff, shift_half_val hn heven]
  unfold cycLen
  by_cases h : u.val ≤ v.val
  · rw [Int.natAbs_natCast_sub_natCast_of_le h]
    split_ifs <;> omega
  · rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega : v.val ≤ u.val)]
    split_ifs <;> omega

lemma halfturn_involutive {n : ℕ} (heven : 2 ∣ n) (u : Fin n) :
    shift (shift u (n / 2)) (n / 2) = u := by
  have heq : n / 2 + n / 2 = n := by omega
  rw [shift_shift, heq]
  simpa only [zero_add, shift_zero] using shift_add_n u 0

lemma halfturn_toggles {n : ℕ} (hn : 0 < n) (heven : 2 ∣ n) (u : Fin n) :
    (shift u (n / 2)).val < n / 2 ↔ ¬ u.val < n / 2 := by
  have heq : n / 2 + n / 2 = n := by omega
  rw [shift_half_val hn heven]
  split_ifs <;> omega

lemma lenCount_one_eq_sum {n : ℕ} (hn : 2 < n) (x : Fin n → Fin n → ℝ)
    (hsym : ∀ u v, x u v = x v u) :
    lenCount n 1 x = ∑ u : Fin n, x u (shift u 1) := by
  have hp (u v : Fin n) :
      (if cycLen n u v = 1 then x u v else 0) =
        (if v = shift u 1 then x u v else 0) +
          (if u = shift v 1 then x v u else 0) := by
    by_cases hv : v = shift u 1
    · have hu : ¬ u = shift v 1 := fun hu => short_directions_disjoint hn u v ⟨hv, hu⟩
      rw [if_pos ((cycLen_one_iff hn u v).mpr (Or.inl hv)), if_pos hv, if_neg hu]
      simp
    · by_cases hu : u = shift v 1
      · rw [if_pos ((cycLen_one_iff hn u v).mpr (Or.inr hu)), if_neg hv, if_pos hu]
        simpa only [zero_add] using hsym u v
      · rw [if_neg ((cycLen_one_iff hn u v).not.mpr (not_or.mpr ⟨hv, hu⟩)),
          if_neg hv, if_neg hu]
        simp
  have hf : (∑ u : Fin n, ∑ v : Fin n, if v = shift u 1 then x u v else 0) =
      ∑ u : Fin n, x u (shift u 1) := by simp
  have hb : (∑ u : Fin n, ∑ v : Fin n, if u = shift v 1 then x v u else 0) =
      ∑ u : Fin n, x u (shift u 1) := by rw [Finset.sum_comm]; simp
  have hsum : (∑ u : Fin n, ∑ v : Fin n, if cycLen n u v = 1 then x u v else 0) =
      2 * ∑ u : Fin n, x u (shift u 1) := by
    calc
      _ = ∑ u : Fin n, ∑ v : Fin n,
          ((if v = shift u 1 then x u v else 0) +
            (if u = shift v 1 then x v u else 0)) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        exact hp u v
      _ = _ := by simp only [Finset.sum_add_distrib, hf, hb]; ring
  have h := twice_lenCount 1 (by omega) x hsym
  linarith

lemma twice_lenCount_half_eq_sum {n : ℕ} (hn : 0 < n) (heven : 2 ∣ n)
    (x : Fin n → Fin n → ℝ) (hsym : ∀ u v, x u v = x v u) :
    2 * lenCount n (n / 2) x = ∑ u : Fin n, x u (shift u (n / 2)) := by
  have hhalf : n / 2 ≠ 0 := by omega
  rw [twice_lenCount (n / 2) hhalf x hsym]
  simp only [cycLen_half_iff hn heven]
  simp

-- Copied verbatim from the frozen C2 tour-count helper.
lemma tourVec_symm {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    MetricTSP.tourVec π u v = MetricTSP.tourVec π v u := by
  simp [MetricTSP.tourVec, MetricTSP.tourSteps, or_comm]

lemma sum_window {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) :
    (∑ u : Fin n, window π u) =
      2 * ((∑ u : Fin n, MetricTSP.tourVec π u (shift u 1)) +
        ∑ u : Fin n, MetricTSP.tourVec π u (shift u (n / 2))) := by
  have hs : (∑ u : Fin n, MetricTSP.tourVec π (shift u (n / 2)) (shift u (n / 2 + 1))) =
      ∑ u : Fin n, MetricTSP.tourVec π u (shift u 1) := by
    simpa only [shift_shift] using
      sum_shift hn (n / 2) (fun u => MetricTSP.tourVec π u (shift u 1))
  have hd : (∑ u : Fin n, MetricTSP.tourVec π (shift u 1) (shift u (1 + n / 2))) =
      ∑ u : Fin n, MetricTSP.tourVec π u (shift u (n / 2)) := by
    simpa only [shift_shift] using
      sum_shift hn 1 (fun u => MetricTSP.tourVec π u (shift u (n / 2)))
  simp only [window, Finset.sum_add_distrib, hs, hd]
  ring

lemma window_halfturn {n : ℕ} (heven : 2 ∣ n) (π : Equiv.Perm (Fin n)) (u : Fin n) :
    window π (shift u (n / 2)) = window π u := by
  have hdd : n / 2 + n / 2 = n := by omega
  have hd1 : n / 2 + (n / 2 + 1) = 1 + n := by omega
  have h1d : n / 2 + (1 + n / 2) = 1 + n := by omega
  unfold window
  simp only [shift_shift, hd1, h1d, hdd, shift_add_n]
  have hzero : shift u n = u := by simpa only [zero_add, shift_zero] using shift_add_n u 0
  rw [hzero]
  rw [show n / 2 + 1 = 1 + n / 2 by omega]
  rw [tourVec_symm π (shift u (n / 2)) u]
  rw [tourVec_symm π (shift u (1 + n / 2)) (shift u 1)]
  ring

lemma sum_window_eq_twice_half {n : ℕ} (hn : 0 < n) (heven : 2 ∣ n)
    (π : Equiv.Perm (Fin n)) :
    (∑ u : Fin n, window π u) =
      2 * ∑ u ∈ Finset.univ.filter (fun u : Fin n => u.val < n / 2), window π u := by
  have hpair :
      (∑ u ∈ Finset.univ.filter (fun u : Fin n => u.val < n / 2), window π u) =
        ∑ u ∈ Finset.univ.filter (fun u : Fin n => ¬ u.val < n / 2), window π u := by
    apply Finset.sum_bij (fun u _ => shift u (n / 2))
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      rw [halfturn_toggles hn heven]
      exact not_not.mpr hu
    · intro u hu v hv huv
      exact shift_injective hn (n / 2) huv
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      refine ⟨shift v (n / 2), ?_, halfturn_involutive heven v⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (halfturn_toggles hn heven v).mpr hv
    · intro u hu
      exact (window_halfturn heven π u).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun u : Fin n => u.val < n / 2) (window π)
  linarith

end CircletTSP.Facet.WindowCountProof

open CircletTSP.Facet

theorem solution (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n)) :
    lenCount n 1 (MetricTSP.tourVec π) + 2 * lenCount n (n / 2) (MetricTSP.tourVec π) =
      ∑ u ∈ Finset.univ.filter (fun u : Fin n => u.val < n / 2), window π u := by
  have hn2 : 2 < n := by omega
  have heven : 2 ∣ n := dvd_trans (by decide : 2 ∣ 4) h4
  have hs := WindowCountProof.lenCount_one_eq_sum hn2 (MetricTSP.tourVec π)
    (WindowCountProof.tourVec_symm π)
  have hd := WindowCountProof.twice_lenCount_half_eq_sum hn heven (MetricTSP.tourVec π)
    (WindowCountProof.tourVec_symm π)
  have hw := WindowCountProof.sum_window hn π
  have hh := WindowCountProof.sum_window_eq_twice_half hn heven π
  linarith

