-- Prove2me | solution 1 for BB6Kit.prop39_int
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T06:11:46.346797+00:00
-- url     : https://prove2.me/submissions/c1b31e41-d58c-4bcf-96a6-01b54023df1f

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

open Finset

namespace P39

lemma tri_sum (q : ℕ) : ∑ v ∈ range q, ((q - v : ℕ) : ℝ) = (q:ℝ) * ((q:ℝ) + 1) / 2 := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h : ∑ v ∈ range n, ((n + 1 - v : ℕ) : ℝ) = ∑ v ∈ range n, (((n - v : ℕ) : ℝ) + 1) := by
      apply sum_congr rfl
      intro v hv
      rw [mem_range] at hv
      rw [show n + 1 - v = (n - v) + 1 by omega, Nat.cast_add, Nat.cast_one]
    rw [h, sum_add_distrib, ih, show n + 1 - n = 1 by omega]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
    push_cast
    ring

lemma trunc_bound (L q : ℕ) : ∑ v ∈ range L, ((q - v : ℕ) : ℝ) ≤ (q:ℝ) * ((q:ℝ) + 1) / 2 := by
  rw [← tri_sum q]
  calc ∑ v ∈ range L, ((q - v : ℕ) : ℝ) = ∑ v ∈ (range L).filter (· < q), ((q - v : ℕ) : ℝ) := by
        rw [sum_filter]
        apply sum_congr rfl
        intro v _
        split_ifs with h
        · rfl
        · have : q - v = 0 := by omega
          simp [this]
    _ ≤ ∑ v ∈ range q, ((q - v : ℕ) : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro v hv
          simp only [mem_filter, mem_range] at hv ⊢
          exact hv.2
        · intro v _ _
          exact Nat.cast_nonneg _

/-- Inner bound: `s` indices whose `ℓ`-values have multiplicity at most `A` carry `ℓ`-sum at least `s²/(2A) - s/2`. -/
lemma inner (N L : ℕ) (A : ℝ) (hA : 0 < A) (ℓ : Fin N → ℕ)
    (hℓ : ∀ f : ℕ → ℝ, (∀ v, 0 ≤ f v) → ∑ i, f (ℓ i) ≤ A * ∑ v ∈ range L, f v)
    (S : Finset (Fin N)) :
    ((S.card : ℝ)) ^ 2 / (2 * A) - (S.card : ℝ) / 2 ≤ ∑ i ∈ S, (ℓ i : ℝ) := by
  have hs0 : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
  obtain ⟨q, hq1, hq2⟩ : ∃ q : ℕ, (q:ℝ) * A ≤ S.card ∧ (S.card:ℝ) < ((q:ℝ) + 1) * A := by
    refine ⟨⌊(S.card:ℝ) / A⌋₊, ?_, ?_⟩
    · have := Nat.floor_le (div_nonneg hs0 hA.le)
      rwa [le_div_iff₀ hA] at this
    · have := Nat.lt_floor_add_one ((S.card:ℝ) / A)
      rwa [div_lt_iff₀ hA] at this
  have hpt : ∀ i, (q:ℝ) - ((q - ℓ i : ℕ) : ℝ) ≤ (ℓ i : ℝ) := by
    intro i
    rcases le_total (ℓ i) q with h | h
    · rw [Nat.cast_sub h]; linarith
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, sub_zero]; exact_mod_cast h
  have h1 : ∑ i ∈ S, ((q:ℝ) - ((q - ℓ i : ℕ) : ℝ)) ≤ ∑ i ∈ S, (ℓ i : ℝ) :=
    sum_le_sum (fun i _ => hpt i)
  have h2 : ∑ i ∈ S, ((q - ℓ i : ℕ) : ℝ) ≤ ∑ i, ((q - ℓ i : ℕ) : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun i _ _ => Nat.cast_nonneg _)
  have h3 : ∑ i, ((q - ℓ i : ℕ) : ℝ) ≤ A * ((q:ℝ) * ((q:ℝ) + 1) / 2) := by
    calc ∑ i, ((q - ℓ i : ℕ) : ℝ) ≤ A * ∑ v ∈ range L, ((q - v : ℕ) : ℝ) :=
          hℓ (fun v => ((q - v : ℕ) : ℝ)) (fun v => Nat.cast_nonneg _)
      _ ≤ A * ((q:ℝ) * ((q:ℝ) + 1) / 2) := mul_le_mul_of_nonneg_left (trunc_bound L q) hA.le
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul] at h1
  have key : ((S.card : ℝ)) ^ 2 / (2 * A) - (S.card : ℝ) / 2 ≤
      (S.card:ℝ) * q - A * ((q:ℝ) * ((q:ℝ) + 1) / 2) := by
    rw [div_sub_div _ _ (ne_of_gt (by linarith : (0:ℝ) < 2 * A)) (by norm_num),
      div_le_iff₀ (by linarith : (0:ℝ) < 2 * A * 2)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr hq2.le)]
  linarith

lemma step (y m t : ℝ) (hm : 0 < m) :
    2 * ((max 0 (y - t * m)) ^ 3 - (max 0 (y - (t + 1) * m)) ^ 3) ≤
      3 * m * ((max 0 (y - t * m)) ^ 2 + (max 0 (y - (t + 1) * m)) ^ 2) := by
  rcases le_total (y - (t + 1) * m) 0 with h1 | h1
  · rw [max_eq_left h1]
    rcases le_total (y - t * m) 0 with h2 | h2
    · rw [max_eq_left h2]; norm_num
    · rw [max_eq_right h2]
      have ha : y - t * m ≤ m := by linarith
      nlinarith [mul_nonneg (mul_nonneg h2 h2) (sub_nonneg.mpr ha), mul_nonneg (mul_nonneg h2 h2) hm.le]
  · have h2 : 0 ≤ y - t * m := by linarith
    rw [max_eq_right h1, max_eq_right h2]
    have e : y - t * m = (y - (t + 1) * m) + m := by ring
    rw [e]
    nlinarith [pow_pos hm 3, h1]

lemma pt (a b d : ℝ) (ha : a ≤ d) (hb : b ≤ -d) (hab : a + b ≤ 0) :
    (max 0 b) ^ 2 + (max 0 a) ^ 2 ≤ d ^ 2 := by
  rcases le_total a 0 with h1 | h1 <;> rcases le_total b 0 with h2 | h2
  · rw [max_eq_left h1, max_eq_left h2]; nlinarith [sq_nonneg d]
  · rw [max_eq_left h1, max_eq_right h2]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -d - b) (by linarith : (0:ℝ) ≤ -d + b)]
  · rw [max_eq_right h1, max_eq_left h2]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - a) (by linarith : (0:ℝ) ≤ d + a)]
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    rw [max_eq_right h1, max_eq_right h2, ha0, hb0]
    nlinarith [sq_nonneg d]

noncomputable def gfun (y m : ℝ) (v : ℕ) : ℝ := (max 0 (y - (v:ℝ) * m)) ^ 2
noncomputable def hfun (y m : ℝ) (v : ℕ) : ℝ := (max 0 (y - (v:ℝ) * m)) ^ 3

/-- Trapezoid bound for the convex function `t ↦ max(0, y - t m)²`. -/
lemma trap (y m : ℝ) (hm : 0 < m) (hy : 0 ≤ y) (X : ℕ) (hX : y ≤ (X:ℝ) * m) :
    2 * y ^ 3 / (3 * m) ≤ 2 * ∑ v ∈ range X, gfun y m v - y ^ 2 := by
  have hst : ∀ v ∈ range X, 2 * (hfun y m v - hfun y m (v + 1)) ≤
      3 * m * (gfun y m v + gfun y m (v + 1)) := by
    intro v _
    have := step y m (v:ℝ) hm
    simp only [gfun, hfun]
    push_cast
    linarith
  have hsum := sum_le_sum hst
  rw [← mul_sum, ← mul_sum, sum_add_distrib, sum_range_sub'] at hsum
  have e2 : ∑ v ∈ range X, gfun y m (v + 1) =
      ∑ v ∈ range X, gfun y m v + gfun y m X - gfun y m 0 := by
    have a1 := sum_range_succ' (gfun y m) X
    have a2 := sum_range_succ (gfun y m) X
    linarith
  rw [e2] at hsum
  have h0 : hfun y m 0 = y ^ 3 := by
    unfold hfun; rw [Nat.cast_zero, zero_mul, sub_zero, max_eq_right hy]
  have hX' : hfun y m X = 0 := by
    unfold hfun; rw [max_eq_left (show y - (X:ℝ) * m ≤ 0 by linarith)]; norm_num
  have g0 : gfun y m 0 = y ^ 2 := by
    unfold gfun; rw [Nat.cast_zero, zero_mul, sub_zero, max_eq_right hy]
  have gX : gfun y m X = 0 := by
    unfold gfun; rw [max_eq_left (show y - (X:ℝ) * m ≤ 0 by linarith)]; norm_num
  rw [h0, hX', g0, gX] at hsum
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 3 * m)]
  nlinarith [hsum]

/-- Outer bound: profiles `s_v` constrained by multiplicity `m` stay far from `N/2` on average. -/
lemma outer (N X : ℕ) (m : ℝ) (hm : 0 < m) (hN : (N:ℝ) ≤ X * m) (s : ℕ → ℝ)
    (hs1 : ∀ v ∈ range X, s v ≤ m * ((X:ℝ) - 1 - v))
    (hs2 : ∀ v ∈ range X, (N:ℝ) - s v ≤ m * ((v:ℝ) + 1)) :
    (N:ℝ) ^ 3 / (12 * m) ≤ ∑ v ∈ range X, ((N:ℝ) / 2 - s v) ^ 2 := by
  have hy : (0:ℝ) ≤ (N:ℝ) / 2 := by positivity
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hyX : (N:ℝ) / 2 ≤ X * m := by linarith
  have hpt : ∀ v ∈ range X, gfun ((N:ℝ) / 2) m (v + 1) + gfun ((N:ℝ) / 2) m (X - 1 - v) ≤
      ((N:ℝ) / 2 - s v) ^ 2 := by
    intro v hv
    have hvX : v < X := mem_range.mp hv
    have hc : ((X - 1 - v : ℕ) : ℝ) = (X:ℝ) - 1 - v := by
      rw [Nat.cast_sub (show v ≤ X - 1 by omega), Nat.cast_sub (show 1 ≤ X by omega), Nat.cast_one]
    simp only [gfun]
    rw [hc]
    push_cast
    have h1 := hs1 v hv
    have h2 := hs2 v hv
    exact pt _ _ _ (by linarith) (by linarith) (by linarith)
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib, sum_range_reflect (gfun ((N:ℝ) / 2) m) X] at hsum
  have e2 : ∑ v ∈ range X, gfun ((N:ℝ) / 2) m (v + 1) =
      ∑ v ∈ range X, gfun ((N:ℝ) / 2) m v + gfun ((N:ℝ) / 2) m X - gfun ((N:ℝ) / 2) m 0 := by
    have a1 := sum_range_succ' (gfun ((N:ℝ) / 2) m) X
    have a2 := sum_range_succ (gfun ((N:ℝ) / 2) m) X
    linarith
  have gX : 0 ≤ gfun ((N:ℝ) / 2) m X := by unfold gfun; positivity
  have g0 : gfun ((N:ℝ) / 2) m 0 = ((N:ℝ) / 2) ^ 2 := by
    unfold gfun; rw [Nat.cast_zero, zero_mul, sub_zero, max_eq_right hy]
  have ht := trap ((N:ℝ) / 2) m hm hy X hyX
  rw [e2, g0] at hsum
  have : (N:ℝ) ^ 3 / (12 * m) = 2 * ((N:ℝ) / 2) ^ 3 / (3 * m) := by ring
  rw [this]
  linarith

noncomputable def cnt {N : ℕ} (x : Fin N → ℕ) (v : ℕ) : ℝ :=
  (((univ.filter (fun i : Fin N => v < x i)).card : ℕ) : ℝ)

/-- Rearrangement bound (Lemme 4 of Laurent–Mignotte–Nesterenko, as used in Lemma 3.2 of the kit). -/
lemma rearr (N L X : ℕ) (A m : ℝ) (hN0 : 0 < N) (hA : 0 < A) (hm : 0 < m)
    (hNA : (N:ℝ) = A * L) (hNX : (N:ℝ) ≤ X * m) (ℓ x : Fin N → ℕ)
    (hℓ : ∀ f : ℕ → ℝ, (∀ v, 0 ≤ f v) → ∑ i, f (ℓ i) ≤ A * ∑ v ∈ range L, f v)
    (hx : ∀ f : ℕ → ℝ, (∀ v, 0 ≤ f v) → ∑ i, f (x i) ≤ m * ∑ v ∈ range X, f v) :
    ((L:ℝ) - 1) / 2 * ∑ i, (x i : ℝ) - (N:ℝ) * L * X * (1 / 4 - N / (12 * (X * m))) / 2
      ≤ ∑ i, ((ℓ i : ℝ) * (x i : ℝ)) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN0
  have hX : (0:ℝ) < X := by
    rcases Nat.eq_zero_or_pos X with h | h
    · rw [h, Nat.cast_zero, zero_mul] at hNX; linarith
    · exact_mod_cast h
  have hxlt : ∀ i, x i < X := by
    have h0 := hx (fun v => if X ≤ v then 1 else 0) (fun v => by split_ifs <;> norm_num)
    beta_reduce at h0
    have hz : ∑ v ∈ range X, (if X ≤ v then (1:ℝ) else 0) = 0 := by
      apply sum_eq_zero
      intro v hv
      rw [mem_range] at hv
      rw [if_neg (show ¬ X ≤ v by omega)]
    rw [hz, mul_zero] at h0
    intro i
    by_contra hc
    push_neg at hc
    have h1 : (1:ℝ) ≤ ∑ j, (if X ≤ x j then (1:ℝ) else 0) := by
      have := single_le_sum (f := fun j => if X ≤ x j then (1:ℝ) else 0)
        (fun j _ => by split_ifs <;> norm_num) (mem_univ i)
      simp only [if_pos hc] at this
      exact this
    linarith
  have hlay : ∀ i, ((x i : ℕ) : ℝ) = ∑ v ∈ range X, (if v < x i then (1:ℝ) else 0) := by
    intro i
    rw [sum_boole]
    have hf : (range X).filter (fun v => v < x i) = range (x i) := by
      ext v
      simp only [mem_filter, mem_range]
      have := hxlt i
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨by omega, h⟩
    rw [hf, card_range]
  have hxs : ∑ i, (x i : ℝ) = ∑ v ∈ range X, cnt x v := by
    calc ∑ i, (x i : ℝ) = ∑ i, ∑ v ∈ range X, (if v < x i then (1:ℝ) else 0) :=
          sum_congr rfl (fun i _ => hlay i)
      _ = ∑ v ∈ range X, ∑ i, (if v < x i then (1:ℝ) else 0) := sum_comm
      _ = ∑ v ∈ range X, cnt x v := by
          apply sum_congr rfl
          intro v _
          simp only [sum_boole, cnt]
  have hlx : ∑ i, ((ℓ i : ℝ) * (x i : ℝ)) =
      ∑ v ∈ range X, ∑ i ∈ univ.filter (fun i => v < x i), (ℓ i : ℝ) := by
    calc ∑ i, ((ℓ i : ℝ) * (x i : ℝ)) = ∑ i, ∑ v ∈ range X, (if v < x i then (ℓ i : ℝ) else 0) := by
          apply sum_congr rfl
          intro i _
          rw [hlay i, mul_sum]
          apply sum_congr rfl
          intro v _
          split_ifs <;> simp
      _ = ∑ v ∈ range X, ∑ i, (if v < x i then (ℓ i : ℝ) else 0) := sum_comm
      _ = ∑ v ∈ range X, ∑ i ∈ univ.filter (fun i => v < x i), (ℓ i : ℝ) := by
          apply sum_congr rfl
          intro v _
          rw [sum_filter]
  have hs1 : ∀ v ∈ range X, cnt x v ≤ m * ((X:ℝ) - 1 - v) := by
    intro v hv
    have hvX := mem_range.mp hv
    have h := hx (fun w => if v < w then 1 else 0) (fun w => by split_ifs <;> norm_num)
    beta_reduce at h
    rw [sum_boole, sum_boole] at h
    have hf : (range X).filter (fun w => v < w) = Ioo v X := by
      ext w
      simp only [mem_filter, mem_range, mem_Ioo]
      constructor
      · intro h; exact ⟨h.2, h.1⟩
      · intro h; exact ⟨h.2, h.1⟩
    rw [hf, Nat.card_Ioo] at h
    have hc : ((X - v - 1 : ℕ) : ℝ) = (X:ℝ) - 1 - v := by
      rw [Nat.cast_sub (show 1 ≤ X - v by omega), Nat.cast_sub (show v ≤ X by omega), Nat.cast_one]
      ring
    rw [hc] at h
    exact h
  have hs2 : ∀ v ∈ range X, (N:ℝ) - cnt x v ≤ m * ((v:ℝ) + 1) := by
    intro v _
    have h := hx (fun w => if v < w then 0 else 1) (fun w => by split_ifs <;> norm_num)
    beta_reduce at h
    have e1 : ∑ i, (if v < x i then (0:ℝ) else 1) = (N:ℝ) - cnt x v := by
      have : ∀ i, (if v < x i then (0:ℝ) else 1) = 1 - (if v < x i then 1 else 0) := by
        intro i; split_ifs <;> norm_num
      rw [sum_congr rfl (fun i _ => this i), sum_sub_distrib, sum_boole]
      simp [cnt]
    have e2 : ∑ w ∈ range X, (if v < w then (0:ℝ) else 1) ≤ (v:ℝ) + 1 := by
      have : ∑ w ∈ range X, (if v < w then (0:ℝ) else 1) =
          (((range X).filter (fun w => ¬ v < w)).card : ℝ) := by
        rw [← sum_boole]
        apply sum_congr rfl
        intro w _
        by_cases hw : v < w <;> simp [hw]
      rw [this]
      have h3 : ((range X).filter (fun w => ¬ v < w)).card ≤ (range (v + 1)).card :=
        card_le_card (by
          intro w hw
          simp only [mem_filter, mem_range] at hw ⊢
          omega)
      rw [card_range] at h3
      exact_mod_cast h3
    rw [e1] at h
    have := mul_le_mul_of_nonneg_left e2 hm.le
    linarith
  have hT : ∀ v ∈ range X, (cnt x v) ^ 2 / (2 * A) - cnt x v / 2 ≤
      ∑ i ∈ univ.filter (fun i => v < x i), (ℓ i : ℝ) := by
    intro v _
    exact inner N L A hA ℓ hℓ _
  have hsT := sum_le_sum hT
  have hout := outer N X m hm hNX (cnt x) hs1 hs2
  rw [hxs, hlx]
  rw [sum_sub_distrib, ← sum_div, ← sum_div] at hsT
  have hexp : ∑ v ∈ range X, ((N:ℝ) / 2 - cnt x v) ^ 2 =
      (X:ℝ) * ((N:ℝ) / 2) ^ 2 - N * ∑ v ∈ range X, cnt x v + ∑ v ∈ range X, (cnt x v) ^ 2 := by
    have : ∀ v ∈ range X, ((N:ℝ) / 2 - cnt x v) ^ 2 =
        ((N:ℝ) / 2) ^ 2 - N * cnt x v + (cnt x v) ^ 2 := by
      intro v _; ring
    rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_range,
      nsmul_eq_mul]
  rw [hexp] at hout
  have hXne : (X:ℝ) ≠ 0 := hX.ne'
  have hmne : m ≠ 0 := hm.ne'
  have hAne : A ≠ 0 := hA.ne'
  have hG : (N:ℝ) * L * X * (1 / 4 - N / (12 * (X * m))) / 2 =
      ((X:ℝ) * (N:ℝ) ^ 2 / 4 - (N:ℝ) ^ 3 / (12 * m)) / (2 * A) := by
    rw [hNA]
    first
    | (field_simp; ring)
    | field_simp
  rw [hG]
  have hinv : 0 ≤ (2 * A)⁻¹ := inv_nonneg.mpr (by linarith)
  have h1 : ((N:ℝ) * ∑ v ∈ range X, cnt x v - ∑ v ∈ range X, (cnt x v) ^ 2) * (2 * A)⁻¹ ≤
      ((X:ℝ) * (N:ℝ) ^ 2 / 4 - (N:ℝ) ^ 3 / (12 * m)) * (2 * A)⁻¹ :=
    mul_le_mul_of_nonneg_right (by linarith) hinv
  rw [← div_eq_mul_inv, ← div_eq_mul_inv] at h1
  have h2 : ((N:ℝ) * ∑ v ∈ range X, cnt x v - ∑ v ∈ range X, (cnt x v) ^ 2) / (2 * A) =
      (L:ℝ) * (∑ v ∈ range X, cnt x v) / 2 - (∑ v ∈ range X, (cnt x v) ^ 2) / (2 * A) := by
    rw [hNA]
    first
    | (field_simp; ring)
    | field_simp
  linarith

end P39

open P39 in
theorem solution (K L R S T N b1 b2 b3 α1 α2 α3 : ℕ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 ≤ α1) (hα2 : 1 ≤ α2) (hα3 : 1 ≤ α3)
    (kml rst : Fin N → ℕ × ℕ × ℕ) (hrows : BB6Kit.RowsOK K L N kml) (hcols : BB6Kit.ColsOK R S T N rst)
    (hne : BB6Delta.deltaR N (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) α1 α2 α3 kml rst ≠ 0) :
    BB6Kit.MK L N rst Prod.fst * Real.log (α1 : ℝ) + BB6Kit.MK L N rst (fun x => x.2.1) * Real.log (α2 : ℝ) + BB6Kit.MK L N rst (fun x => x.2.2) * Real.log (α3 : ℝ) - (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) + BB6Kit.GK N L R S T T * Real.log (α3 : ℝ)) ≤ Real.log |BB6Delta.deltaR N (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) α1 α2 α3 kml rst| := by
  generalize b1 / Nat.gcd b1 b3 = c1 at hne ⊢
  generalize b3 / Nat.gcd b1 b3 = c2 at hne ⊢
  generalize b2 / Nat.gcd b2 b3 = c3 at hne ⊢
  generalize b3 / Nat.gcd b2 b3 = c4 at hne ⊢
  -- basic positivity
  have hNpos : 0 < N := by
    rw [hN]
    refine Nat.div_pos ?_ (by norm_num)
    have : 3 * 4 * 5 ≤ K * (K + 1) * L := Nat.mul_le_mul (Nat.mul_le_mul hK (by omega)) hL
    omega
  have hprod : 0 < R * S * T := lt_of_lt_of_le hNpos hRST
  have hR : 0 < R := Nat.pos_of_ne_zero (by rintro rfl; simp at hprod)
  have hS : 0 < S := Nat.pos_of_ne_zero (by rintro rfl; simp at hprod)
  have hT : 0 < T := Nat.pos_of_ne_zero (by rintro rfl; simp at hprod)
  have hRr : (0:ℝ) < R := by exact_mod_cast hR
  have hSr : (0:ℝ) < S := by exact_mod_cast hS
  have hTr : (0:ℝ) < T := by exact_mod_cast hT
  have hKr : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hA : (0:ℝ) < (K:ℝ) * ((K:ℝ) + 1) / 2 := div_pos (mul_pos hKr (by linarith)) (by norm_num)
  have hNA : (N:ℝ) = ((K:ℝ) * ((K:ℝ) + 1) / 2) * L := by
    have hdvd : 2 ∣ K * (K + 1) * L := (Nat.even_mul_succ_self K).two_dvd.mul_right L
    rw [hN, Nat.cast_div hdvd (by norm_num : ((2:ℕ):ℝ) ≠ 0)]
    push_cast
    ring
  have hRSTr : (N:ℝ) ≤ (R:ℝ) * S * T := by exact_mod_cast hRST
  have hNX1 : (N:ℝ) ≤ R * ((S:ℝ) * T) := by linarith
  have hNX2 : (N:ℝ) ≤ S * ((R:ℝ) * T) := by linarith
  have hNX3 : (N:ℝ) ≤ T * ((R:ℝ) * S) := by linarith
  -- rows: each ℓ-value has multiplicity at most K(K+1)/2
  have hrow : ∀ f : ℕ → ℝ, (∀ v, 0 ≤ f v) →
      ∑ i, f ((kml i).2.2) ≤ ((K:ℝ) * ((K:ℝ) + 1) / 2) * ∑ v ∈ range L, f v := by
    intro f hf
    have e1 : ∑ p ∈ univ.image kml, f p.2.2 = ∑ i, f ((kml i).2.2) :=
      sum_image (by intro x _ y _ h; exact hrows.1 h)
    have e2 : ∑ p ∈ univ.image kml, f p.2.2 ≤ ∑ p ∈ BB6Kit.rowSet K L, f p.2.2 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [mem_image] at hp
        obtain ⟨i, _, rfl⟩ := hp
        exact hrows.2 i
      · intro p _ _
        exact hf _
    have e3 : ∑ p ∈ BB6Kit.rowSet K L, f p.2.2 = ((K:ℝ) * ((K:ℝ) + 1) / 2) * ∑ v ∈ range L, f v := by
      unfold BB6Kit.rowSet
      rw [sum_filter, sum_product]
      trans ∑ k ∈ range K, ((K - k : ℕ) : ℝ) * ∑ v ∈ range L, f v
      · apply sum_congr rfl
        intro k hk
        rw [mem_range] at hk
        rw [sum_product]
        try dsimp only
        have h2 : ∀ mm ∈ range K, ∑ v ∈ range L, (if k + mm ≤ K - 1 then f v else 0) =
            (if mm < K - k then (1:ℝ) else 0) * ∑ v ∈ range L, f v := by
          intro mm hmm
          rw [mem_range] at hmm
          by_cases hc : mm < K - k
          · rw [if_pos hc, one_mul]
            apply sum_congr rfl
            intro v _
            rw [if_pos (show k + mm ≤ K - 1 by omega)]
          · rw [if_neg hc, zero_mul]
            apply sum_eq_zero
            intro v _
            rw [if_neg (show ¬ (k + mm ≤ K - 1) by omega)]
        rw [sum_congr rfl h2, ← sum_mul, sum_boole]
        congr 1
        have hf2 : (range K).filter (fun mm => mm < K - k) = range (K - k) := by
          ext mm
          simp only [mem_filter, mem_range]
          constructor
          · intro h; exact h.2
          · intro h; exact ⟨by omega, h⟩
        rw [hf2, card_range]
      · rw [← sum_mul, tri_sum K]
    linarith [e1, e2, e3]
  have hℓσ : ∀ σ : Equiv.Perm (Fin N), ∀ f : ℕ → ℝ, (∀ v, 0 ≤ f v) →
      ∑ i, f ((kml (σ i)).2.2) ≤ ((K:ℝ) * ((K:ℝ) + 1) / 2) * ∑ v ∈ range L, f v :=
    fun σ f hf => (Equiv.sum_comp σ (fun i => f ((kml i).2.2))).trans_le (hrow f hf)
  -- columns: multiplicities bounded by the other two box sides
  have hbox : ∀ F : ℕ × ℕ × ℕ → ℝ, (∀ p, 0 ≤ F p) →
      ∑ j, F (rst j) ≤ ∑ p ∈ range R ×ˢ range S ×ˢ range T, F p := by
    intro F hF
    have e1 : ∑ p ∈ univ.image rst, F p = ∑ j, F (rst j) :=
      sum_image (by intro x _ y _ h; exact hcols.1 h)
    rw [← e1]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [mem_image] at hp
      obtain ⟨j, _, rfl⟩ := hp
      obtain ⟨h1, h2, h3⟩ := hcols.2 j
      simp only [mem_product, mem_range]
      exact ⟨h1, h2, h3⟩
    · intro p _ _
      exact hF p
  have hcol1 : ∀ f : ℕ → ℝ, (∀ v, 0 ≤ f v) →
      ∑ j, f ((rst j).1) ≤ ((S:ℝ) * T) * ∑ v ∈ range R, f v := by
    intro f hf
    refine le_trans (hbox (fun p => f p.1) (fun p => hf _)) (le_of_eq ?_)
    (simp only [sum_product, sum_const, card_range, card_product, Nat.cast_mul, nsmul_eq_mul, ← mul_sum]) <;> ring
  have hcol2 : ∀ f : ℕ → ℝ, (∀ v, 0 ≤ f v) →
      ∑ j, f ((rst j).2.1) ≤ ((R:ℝ) * T) * ∑ v ∈ range S, f v := by
    intro f hf
    refine le_trans (hbox (fun p => f p.2.1) (fun p => hf _)) (le_of_eq ?_)
    (simp only [sum_product, sum_const, card_range, card_product, Nat.cast_mul, nsmul_eq_mul, ← mul_sum]) <;> ring
  have hcol3 : ∀ f : ℕ → ℝ, (∀ v, 0 ≤ f v) →
      ∑ j, f ((rst j).2.2) ≤ ((R:ℝ) * S) * ∑ v ∈ range T, f v := by
    intro f hf
    refine le_trans (hbox (fun p => f p.2.2) (fun p => hf _)) (le_of_eq ?_)
    (simp only [sum_product, sum_const, card_range, card_product, Nat.cast_mul, nsmul_eq_mul, ← mul_sum]) <;> ring
  -- the rearrangement bound for each coordinate and each permutation
  have hr1 : ∀ σ : Equiv.Perm (Fin N), BB6Kit.MK L N rst Prod.fst - BB6Kit.GK N L R S T R ≤
      ∑ i, ((kml (σ i)).2.2 : ℝ) * ((rst i).1 : ℝ) := by
    intro σ
    have r := rearr N L R _ ((S:ℝ) * T) hNpos hA (mul_pos hSr hTr) hNA hNX1
      (fun i => (kml (σ i)).2.2) (fun j => (rst j).1) (hℓσ σ) hcol1
    have hG : BB6Kit.GK N L R S T R = (N:ℝ) * L * R * (1 / 4 - N / (12 * (R * ((S:ℝ) * T)))) / 2 := by
      unfold BB6Kit.GK BB6Kit.gK; ring
    rw [hG]
    exact r
  have hr2 : ∀ σ : Equiv.Perm (Fin N), BB6Kit.MK L N rst (fun x => x.2.1) - BB6Kit.GK N L R S T S ≤
      ∑ i, ((kml (σ i)).2.2 : ℝ) * ((rst i).2.1 : ℝ) := by
    intro σ
    have r := rearr N L S _ ((R:ℝ) * T) hNpos hA (mul_pos hRr hTr) hNA hNX2
      (fun i => (kml (σ i)).2.2) (fun j => (rst j).2.1) (hℓσ σ) hcol2
    have hG : BB6Kit.GK N L R S T S = (N:ℝ) * L * S * (1 / 4 - N / (12 * (S * ((R:ℝ) * T)))) / 2 := by
      unfold BB6Kit.GK BB6Kit.gK; ring
    rw [hG]
    exact r
  have hr3 : ∀ σ : Equiv.Perm (Fin N), BB6Kit.MK L N rst (fun x => x.2.2) - BB6Kit.GK N L R S T T ≤
      ∑ i, ((kml (σ i)).2.2 : ℝ) * ((rst i).2.2 : ℝ) := by
    intro σ
    have r := rearr N L T _ ((R:ℝ) * S) hNpos hA (mul_pos hRr hSr) hNA hNX3
      (fun i => (kml (σ i)).2.2) (fun j => (rst j).2.2) (hℓσ σ) hcol3
    have hG : BB6Kit.GK N L R S T T = (N:ℝ) * L * T * (1 / 4 - N / (12 * (T * ((R:ℝ) * S)))) / 2 := by
      unfold BB6Kit.GK BB6Kit.gK; ring
    rw [hG]
    exact r
  -- integer exponents
  set m1 : ℕ := ⌈BB6Kit.MK L N rst Prod.fst - BB6Kit.GK N L R S T R⌉₊ with hm1def
  set m2 : ℕ := ⌈BB6Kit.MK L N rst (fun x => x.2.1) - BB6Kit.GK N L R S T S⌉₊ with hm2def
  set m3 : ℕ := ⌈BB6Kit.MK L N rst (fun x => x.2.2) - BB6Kit.GK N L R S T T⌉₊ with hm3def
  have hm1 : ∀ σ : Equiv.Perm (Fin N), m1 ≤ ∑ i, (kml (σ i)).2.2 * (rst i).1 :=
    fun σ => Nat.ceil_le.mpr (by push_cast; exact hr1 σ)
  have hm2 : ∀ σ : Equiv.Perm (Fin N), m2 ≤ ∑ i, (kml (σ i)).2.2 * (rst i).2.1 :=
    fun σ => Nat.ceil_le.mpr (by push_cast; exact hr2 σ)
  have hm3 : ∀ σ : Equiv.Perm (Fin N), m3 ≤ ∑ i, (kml (σ i)).2.2 * (rst i).2.2 :=
    fun σ => Nat.ceil_le.mpr (by push_cast; exact hr3 σ)
  -- Δ as an integer determinant, divisible by α1^m1 α2^m2 α3^m3
  have key : BB6Delta.deltaR N c1 c2 c3 c4 α1 α2 α3 kml rst =
      (BB6Delta.deltaZ N c1 c2 c3 c4 α1 α2 α3 kml rst : ℝ) := by
    unfold BB6Delta.deltaR BB6Delta.deltaZ
    rw [Int.cast_det]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, BB6Delta.entryNat]
    push_cast
    ring
  have hdvd : ((α1 ^ m1 * α2 ^ m2 * α3 ^ m3 : ℕ) : ℤ) ∣ BB6Delta.deltaZ N c1 c2 c3 c4 α1 α2 α3 kml rst := by
    unfold BB6Delta.deltaZ
    rw [Matrix.det_apply]
    apply Finset.dvd_sum
    intro σ _
    rw [Units.smul_def, smul_eq_mul]
    apply Dvd.dvd.mul_left
    simp only [Matrix.of_apply]
    rw [← Nat.cast_prod]
    apply Int.natCast_dvd_natCast.mpr
    simp only [BB6Delta.entryNat, prod_mul_distrib, prod_pow_eq_pow_sum]
    exact mul_dvd_mul (mul_dvd_mul (Dvd.dvd.mul_left (pow_dvd_pow _ (hm1 σ)) _)
      (pow_dvd_pow _ (hm2 σ))) (pow_dvd_pow _ (hm3 σ))
  have hZ : BB6Delta.deltaZ N c1 c2 c3 c4 α1 α2 α3 kml rst ≠ 0 := by
    intro h0
    apply hne
    rw [key, h0]
    simp
  have hle : ((α1 ^ m1 * α2 ^ m2 * α3 ^ m3 : ℕ) : ℤ) ≤ |BB6Delta.deltaZ N c1 c2 c3 c4 α1 α2 α3 kml rst| :=
    Int.le_of_dvd (abs_pos.mpr hZ) ((dvd_abs _ _).mpr hdvd)
  have hleR : ((α1 ^ m1 * α2 ^ m2 * α3 ^ m3 : ℕ) : ℝ) ≤ |BB6Delta.deltaR N c1 c2 c3 c4 α1 α2 α3 kml rst| := by
    rw [key, ← Int.cast_abs]
    exact_mod_cast hle
  have hcast : ((α1 ^ m1 * α2 ^ m2 * α3 ^ m3 : ℕ) : ℝ) = (α1:ℝ) ^ m1 * (α2:ℝ) ^ m2 * (α3:ℝ) ^ m3 := by
    simp only [Nat.cast_mul, Nat.cast_pow]
  rw [hcast] at hleR
  have ha1 : (0:ℝ) < α1 := by exact_mod_cast (show 0 < α1 by omega)
  have ha2 : (0:ℝ) < α2 := by exact_mod_cast (show 0 < α2 by omega)
  have ha3 : (0:ℝ) < α3 := by exact_mod_cast (show 0 < α3 by omega)
  have p1 := pow_pos ha1 m1
  have p2 := pow_pos ha2 m2
  have p3 := pow_pos ha3 m3
  have hlog := Real.log_le_log (mul_pos (mul_pos p1 p2) p3) hleR
  rw [Real.log_mul (mul_pos p1 p2).ne' p3.ne', Real.log_mul p1.ne' p2.ne', Real.log_pow, Real.log_pow,
    Real.log_pow] at hlog
  have la1 : 0 ≤ Real.log (α1 : ℝ) := Real.log_nonneg (by exact_mod_cast hα1)
  have la2 : 0 ≤ Real.log (α2 : ℝ) := Real.log_nonneg (by exact_mod_cast hα2)
  have la3 : 0 ≤ Real.log (α3 : ℝ) := Real.log_nonneg (by exact_mod_cast hα3)
  have e1 := mul_le_mul_of_nonneg_right (Nat.le_ceil (BB6Kit.MK L N rst Prod.fst - BB6Kit.GK N L R S T R)) la1
  have e2 := mul_le_mul_of_nonneg_right (Nat.le_ceil (BB6Kit.MK L N rst (fun x => x.2.1) - BB6Kit.GK N L R S T S)) la2
  have e3 := mul_le_mul_of_nonneg_right (Nat.le_ceil (BB6Kit.MK L N rst (fun x => x.2.2) - BB6Kit.GK N L R S T T)) la3
  rw [← hm1def] at e1
  rw [← hm2def] at e2
  rw [← hm3def] at e3
  linarith [e1, e2, e3, hlog]
