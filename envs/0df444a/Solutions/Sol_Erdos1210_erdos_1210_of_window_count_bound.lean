-- Prove2me | solution 1 for Erdos1210.erdos_1210_of_window_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:40:30.513114+00:00
-- url     : https://prove2.me/submissions/e7699cc5-f6ed-4921-835f-4313eb55cc27

import Mathlib
open Finset

namespace Erdos1210Partial

lemma reciprocal_layer (s N : ℕ) (_hs : 1 ≤ s) (hsN : s ≤ N) :
    (1 / (s : ℝ)) = 1 / ((N : ℝ) + 1) +
      ∑ x ∈ Icc s N, (1 / (x : ℝ) - 1 / ((x : ℝ) + 1)) := by
  have h := Finset.sum_Ico_sub (fun x : ℕ => 1 / (x : ℝ)) (show s ≤ N + 1 by omega)
  simp only [Nat.cast_add, Nat.cast_one] at h
  have hi : Icc s N = Ico s (N + 1) := by ext x; simp
  rw [hi]
  have hn : ∑ x ∈ Ico s (N + 1), (1 / (x : ℝ) - 1 / ((x : ℝ) + 1)) =
      -(∑ x ∈ Ico s (N + 1), (1 / ((x : ℝ) + 1) - 1 / (x : ℝ))) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intros
    ring
  rw [hn, h]
  ring

lemma reciprocal_count_formula (S : Finset ℕ) (N : ℕ)
    (hS : ∀ s ∈ S, 1 ≤ s ∧ s ≤ N) :
    (∑ s ∈ S, 1 / (s : ℝ)) = (S.card : ℝ) / ((N : ℝ) + 1) +
      ∑ x ∈ Icc 1 N, ((S.filter (fun s => s ≤ x)).card : ℝ) *
        (1 / (x : ℝ) - 1 / ((x : ℝ) + 1)) := by
  have hp (s : ℕ) (hs : s ∈ S) :
      ∑ x ∈ Icc s N, (1 / (x : ℝ) - 1 / ((x : ℝ) + 1)) =
      ∑ x ∈ Icc 1 N, if s ≤ x then
        (1 / (x : ℝ) - 1 / ((x : ℝ) + 1)) else 0 := by
    rw [← sum_filter]
    congr 1
    ext x
    simp only [mem_filter, mem_Icc]
    have := (hS s hs).1
    omega
  calc
    _ = ∑ s ∈ S, (1 / ((N : ℝ) + 1) + ∑ x ∈ Icc 1 N,
          if s ≤ x then (1 / (x : ℝ) - 1 / ((x : ℝ) + 1)) else 0) := by
      apply sum_congr rfl
      intro s hs
      rw [← hp s hs]
      exact reciprocal_layer s N (hS s hs).1 (hS s hs).2
    _ = _ := by
      rw [sum_add_distrib, sum_comm]
      simp only [sum_const, nsmul_eq_mul]
      congr 1
      · ring
      · apply sum_congr rfl
        intro x hx
        rw [← sum_filter, sum_const, nsmul_eq_mul]

lemma first_count_le_one (S : Finset ℕ) (hS : ∀ s ∈ S, 1 ≤ s) :
    ((S.filter (fun s => s ≤ 1)).card : ℝ) ≤ 1 := by
  have hsub : S.filter (fun s => s ≤ 1) ⊆ {1} := by
    intro s hs
    have h := mem_filter.mp hs
    simp only [mem_singleton]
    exact le_antisymm h.2 (hS s h.1)
  exact_mod_cast (card_le_card hsub)

lemma reciprocal_weight_nonneg (x : ℕ) (hx : 1 ≤ x) :
    0 ≤ 1 / (x : ℝ) - 1 / ((x : ℝ) + 1) := by
  have hxp : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  exact sub_nonneg.mpr (one_div_le_one_div_of_le hxp (by linarith))

lemma error_weight (K : ℝ) (x : ℕ) (hx : 1 ≤ x) :
    (K * x / (Real.log x)^2) * (1 / (x : ℝ) - 1 / ((x : ℝ) + 1)) =
      K * (1 / (((x : ℝ) + 1) * (Real.log x)^2)) := by
  have hxp : (x : ℝ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have hxp1 : (x : ℝ) + 1 ≠ 0 := by positivity
  by_cases hl : Real.log x = 0
  · simp [hl]
  · field_simp
    <;> ring

lemma boundary_error (K : ℝ) (hK : 0 ≤ K) (N : ℕ) (hN : 2 ≤ N) :
    (K * N / (Real.log N)^2) / ((N : ℝ) + 1) ≤ K / (Real.log 2)^2 := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hn
  have hd : 0 < (Real.log 2)^2 := sq_pos_of_pos hl2
  have hs : (Real.log 2)^2 ≤ (Real.log N)^2 := by nlinarith
  have ha : K * N / (Real.log N)^2 ≤ K * N / (Real.log 2)^2 :=
    div_le_div_of_nonneg_left (by positivity) hd hs
  calc
    _ ≤ (K * N / (Real.log 2)^2) / ((N : ℝ) + 1) :=
      div_le_div_of_nonneg_right ha (by positivity)
    _ = (K / (Real.log 2)^2) * ((N : ℝ) / ((N : ℝ) + 1)) := by ring
    _ ≤ (K / (Real.log 2)^2) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (div_le_one (by positivity)).mpr (by linarith)
    _ = _ := mul_one _

lemma split_count_sum (f : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ x ∈ Icc 1 N, f x) = f 1 + ∑ x ∈ Icc 2 N, f x := by
  have hi : Icc 1 N = insert 1 (Icc 2 N) := by
    ext x
    simp only [mem_Icc, mem_insert]
    omega
  rw [hi, sum_insert (by simp)]

lemma reciprocal_count_comparison (S T : Finset ℕ) (N : ℕ) (hN : 2 ≤ N)
    (hS : ∀ s ∈ S, 1 ≤ s ∧ s ≤ N) (hT : ∀ s ∈ T, 1 ≤ s ∧ s ≤ N)
    (K : ℝ) (hK : 0 ≤ K)
    (hcount : ∀ x : ℕ, 2 ≤ x → x ≤ N →
      ((S.filter (fun s => s ≤ x)).card : ℝ) ≤
      ((T.filter (fun s => s ≤ x)).card : ℝ) + K * x / (Real.log x)^2) :
    (∑ s ∈ S, 1 / (s : ℝ)) ≤ (∑ t ∈ T, 1 / (t : ℝ)) +
      K / (Real.log 2)^2 + 1 +
      K * ∑ x ∈ Icc 2 N, (1 / (((x : ℝ) + 1) * (Real.log x)^2)) := by
  have hSc : S.filter (fun s => s ≤ N) = S := filter_eq_self.mpr (fun s hs => (hS s hs).2)
  have hTc : T.filter (fun s => s ≤ N) = T := filter_eq_self.mpr (fun s hs => (hT s hs).2)
  have hcard := hcount N hN le_rfl
  rw [hSc, hTc] at hcard
  have hb : (S.card : ℝ) / ((N : ℝ) + 1) ≤
      (T.card : ℝ) / ((N : ℝ) + 1) + K / (Real.log 2)^2 := by
    have hdiv := div_le_div_of_nonneg_right hcard (show (0 : ℝ) ≤ (N : ℝ) + 1 by positivity)
    rw [add_div] at hdiv
    linarith [boundary_error K hK N hN]
  have hfirst :
      ((S.filter (fun s => s ≤ 1)).card : ℝ) * (1 / (1 : ℝ) - 1 / (1 + 1)) ≤
      ((T.filter (fun s => s ≤ 1)).card : ℝ) * (1 / (1 : ℝ) - 1 / (1 + 1)) + 1 := by
    have hf := first_count_le_one S (fun s hs => (hS s hs).1)
    have ht : (0 : ℝ) ≤ (T.filter (fun s => s ≤ 1)).card := by positivity
    norm_num only [Nat.cast_one, div_one, one_add_one_eq_two] at ⊢
    linarith
  have hsum :
      (∑ x ∈ Icc 2 N, ((S.filter (fun s => s ≤ x)).card : ℝ) *
        (1 / (x : ℝ) - 1 / ((x : ℝ) + 1))) ≤
      (∑ x ∈ Icc 2 N, ((T.filter (fun s => s ≤ x)).card : ℝ) *
        (1 / (x : ℝ) - 1 / ((x : ℝ) + 1))) +
        K * ∑ x ∈ Icc 2 N, (1 / (((x : ℝ) + 1) * (Real.log x)^2)) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro x hx
    have hx' := mem_Icc.mp hx
    have hp := mul_le_mul_of_nonneg_right (hcount x hx'.1 hx'.2)
      (reciprocal_weight_nonneg x (by omega))
    rwa [add_mul, error_weight K x (by omega)] at hp
  rw [reciprocal_count_formula S N hS, reciprocal_count_formula T N hT,
    split_count_sum _ N (by omega), split_count_sum _ N (by omega)]
  push_cast
  linarith

lemma prime_count_filter (x N : ℕ) (hx : x ≤ N) :
    ((N.primesLE.filter (fun p => p ≤ x)).card : ℝ) = Nat.primeCounting x := by
  have hf : N.primesLE.filter (fun p => p ≤ x) = x.primesLE := by
    ext p
    simp only [mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, hp⟩, hpx⟩
      exact ⟨hpx, hp⟩
    · rintro ⟨hpx, hp⟩
      exact ⟨⟨hpx.trans hx, hp⟩, hpx⟩
  rw [hf, Nat.primesLE_card_eq_primeCounting]

lemma primesLE_reciprocal_le (n : ℕ) :
    (∑ p ∈ n.primesLE, 1 / (p : ℝ)) ≤
      (∑ p ∈ (range n).filter Nat.Prime, 1 / (p : ℝ)) + 1 := by
  change (∑ p ∈ (n + 1).primesBelow, 1 / (p : ℝ)) ≤
      (∑ p ∈ n.primesBelow, 1 / (p : ℝ)) + 1
  rw [Nat.primesBelow_succ]
  split_ifs with hp
  · rw [sum_insert (Nat.notMem_primesBelow n)]
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast hp.one_le
    have hi : 1 / (n : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hn
    linarith
  · linarith

lemma image_window_count (n x : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, a < n) :
    (((A.image (fun a => n - a)).filter (fun s => s ≤ x)).card : ℝ) =
      ((A.filter (fun a => n - x ≤ a)).card : ℝ) := by
  rw [filter_image]
  have hf : A.filter (fun a => n - a ≤ x) = A.filter (fun a => n - x ≤ a) := by
    apply filter_congr
    intro a ha
    have := hA a ha
    omega
  rw [hf, card_image_of_injOn]
  intro a ha b hb hab
  have h1 := hA a (mem_filter.mp ha).1
  have h2 := hA b (mem_filter.mp hb).1
  change n - a = n - b at hab
  omega

end Erdos1210Partial

namespace ImpactErdos1210

theorem log_error_le_telescope (x : ℝ) (hx : 2 ≤ x) :
    1 / ((x + 1) * (Real.log x) ^ 2) ≤
      2 * (1 / Real.log x - 1 / Real.log (x + 1)) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hm : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
  have hlog : Real.log (x + 1) ≤ 2 * Real.log x := by
    calc
      Real.log (x + 1) ≤ Real.log (x ^ 2) :=
        Real.log_le_log hx1 (by nlinarith)
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have hdiff : 1 / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hx1 hx0)
    rw [Real.log_div hx1.ne' hx0.ne'] at h
    convert h using 1
    field_simp
    ring
  have hgap : 1 ≤ (Real.log (x + 1) - Real.log x) * (x + 1) :=
    (div_le_iff₀ hx1).mp hdiff
  have hbound : Real.log (x + 1) ≤
      2 * Real.log x * ((Real.log (x + 1) - Real.log x) * (x + 1)) := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * Real.log x by positivity)
      (sub_nonneg.mpr hgap)]
  have hbound' := mul_le_mul_of_nonneg_left hbound hl.le
  have hrewrite : 2 * (1 / Real.log x - 1 / Real.log (x + 1)) =
      (2 * (Real.log (x + 1) - Real.log x)) /
        (Real.log x * Real.log (x + 1)) := by
    field_simp
  rw [hrewrite, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem sum_log_error_le (N : ℕ) :
    ∑ x ∈ Icc 2 N, 1 / (((x : ℝ) + 1) * (Real.log x) ^ 2) ≤
      2 / Real.log 2 := by
  by_cases hN : 2 ≤ N
  · have hsum :
        ∑ x ∈ Icc 2 N, 1 / (((x : ℝ) + 1) * (Real.log x) ^ 2) ≤
          2 * ∑ x ∈ Icc 2 N,
            (1 / Real.log (x : ℝ) - 1 / Real.log ((x : ℝ) + 1)) := by
      rw [mul_sum]
      apply sum_le_sum
      intro x hx
      exact log_error_le_telescope x (by exact_mod_cast (mem_Icc.mp hx).1)
    have htel : (∑ x ∈ Icc 2 N,
          (1 / Real.log (x : ℝ) - 1 / Real.log ((x : ℝ) + 1))) =
        1 / Real.log 2 - 1 / Real.log ((N : ℝ) + 1) := by
      have h := sum_Icc_sub hN (fun x : ℕ => 1 / Real.log (x : ℝ))
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h
      have := congrArg Neg.neg h
      simpa only [neg_sub, ← sum_neg_distrib] using this
    rw [htel] at hsum
    have hlast : 0 ≤ 1 / Real.log ((N : ℝ) + 1) := by
      apply one_div_nonneg.mpr
      apply Real.log_nonneg
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      linarith
    have htwo : 2 / Real.log 2 = 2 * (1 / Real.log 2) := by ring
    rw [htwo]
    linarith
  · have hlt : N < 2 := by omega
    rw [Icc_eq_empty_of_lt hlt, sum_empty]
    positivity

end ImpactErdos1210


open Erdos1210Partial

theorem solution
    (h : ∃ K : ℝ, ∀ n : ℕ, ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a < n) →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.Coprime b) →
      ∀ x : ℕ, 2 ≤ x →
        ((A.filter (fun a => n - x ≤ a)).card : ℝ) ≤
          (Nat.primeCounting x : ℝ) + K * x / (Real.log x) ^ 2) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a < n) →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.Coprime b) →
      ∑ a ∈ A, (1 / ((n : ℝ) - a)) ≤
        (∑ p ∈ (range n).filter Nat.Prime, (1 / (p : ℝ))) + C := by
  obtain ⟨K, hK⟩ := h
  let B : ℝ := max K 0
  have hB : 0 ≤ B := le_max_right _ _
  have hKB : K ≤ B := le_max_left _ _
  refine ⟨B / (Real.log 2)^2 + 2 + B * (2 / Real.log 2), ?_⟩
  intro n A hA hcop
  by_cases hn : 2 ≤ n
  · let S := A.image (fun a => n - a)
    have hS : ∀ s ∈ S, 1 ≤ s ∧ s ≤ n := by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hs
      have := hA a ha
      omega
    have hP : ∀ p ∈ n.primesLE, 1 ≤ p ∧ p ≤ n := by
      intro p hp
      have hpp := Nat.mem_primesLE.mp hp
      exact ⟨hpp.2.one_le, hpp.1⟩
    have hcount : ∀ x : ℕ, 2 ≤ x → x ≤ n →
        ((S.filter (fun s => s ≤ x)).card : ℝ) ≤
        ((n.primesLE.filter (fun p => p ≤ x)).card : ℝ) + B * x / (Real.log x)^2 := by
      intro x hx hxn
      rw [prime_count_filter x n hxn]
      change (((A.image (fun a => n - a)).filter (fun s => s ≤ x)).card : ℝ) ≤ _
      rw [image_window_count n x A (fun a ha => (hA a ha).2)]
      apply (hK n A hA hcop x hx).trans
      gcongr
    have hsum := reciprocal_count_comparison S n.primesLE n hn hS hP B hB hcount
    have herror := mul_le_mul_of_nonneg_left (ImpactErdos1210.sum_log_error_le n) hB
    have hprime := primesLE_reciprocal_le n
    have hidentity : (∑ s ∈ S, 1 / (s : ℝ)) = ∑ a ∈ A, 1 / ((n : ℝ) - a) := by
      change (∑ s ∈ A.image (fun a => n - a), 1 / (s : ℝ)) = _
      rw [sum_image]
      · apply sum_congr rfl
        intro a ha
        rw [Nat.cast_sub (Nat.le_of_lt (hA a ha).2)]
      · intro a ha b hb hab
        have h1 := (hA a ha).2
        have h2 := (hA b hb).2
        change n - a = n - b at hab
        omega
    rw [hidentity] at hsum
    linarith
  · have he : A = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      have := hA a ha
      omega
    rw [he, sum_empty]
    have hp : 0 ≤ ∑ p ∈ (range n).filter Nat.Prime, (1 / (p : ℝ)) := by positivity
    positivity
