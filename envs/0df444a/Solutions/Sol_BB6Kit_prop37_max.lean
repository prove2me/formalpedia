-- Prove2me | solution 1 for BB6Kit.prop37_max
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T07:11:17.830023+00:00
-- url     : https://prove2.me/submissions/f0fffedd-deae-4339-87c4-d14943c324b7

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Definitions.Def_BB6Psi

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

namespace MX

lemma gauss (L : ℕ) : ∑ v ∈ range L, (v : ℝ) = (L : ℝ) * ((L : ℝ) - 1) / 2 := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

lemma rowsum (K L : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ BB6Kit.rowSet K L, f p.2.2 = ((K:ℝ) * ((K:ℝ) + 1) / 2) * ∑ v ∈ range L, f v := by
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
  · rw [← sum_mul, P39.tri_sum K]

/-- Two-sided rearrangement bound (Lemma 3.2 of the kit). -/
lemma rearr_abs (N L X : ℕ) (A m : ℝ) (hN0 : 0 < N) (hA : 0 < A) (hm : 0 < m)
    (hNA : (N:ℝ) = A * L) (hNX : (N:ℝ) ≤ X * m) (ℓ x : Fin N → ℕ) (hℓlt : ∀ i, ℓ i < L)
    (hℓ : ∀ f : ℕ → ℝ, (∀ v, 0 ≤ f v) → ∑ i, f (ℓ i) ≤ A * ∑ v ∈ range L, f v)
    (hx : ∀ f : ℕ → ℝ, (∀ v, 0 ≤ f v) → ∑ i, f (x i) ≤ m * ∑ v ∈ range X, f v) :
    |∑ i, (((ℓ i : ℝ) - ((L : ℝ) - 1) / 2) * (x i : ℝ))| ≤
      (N:ℝ) * L * X * (1 / 4 - N / (12 * (X * m))) / 2 := by
  have lo := P39.rearr N L X A m hN0 hA hm hNA hNX ℓ x hℓ hx
  have hℓ' : ∀ f : ℕ → ℝ, (∀ v, 0 ≤ f v) → ∑ i, f (L - 1 - ℓ i) ≤ A * ∑ v ∈ range L, f v := by
    intro f hf
    have h1 := hℓ (fun v => f (L - 1 - v)) (fun v => hf _)
    beta_reduce at h1
    rw [sum_range_reflect f L] at h1
    exact h1
  have hi := P39.rearr N L X A m hN0 hA hm hNA hNX (fun i => L - 1 - ℓ i) x hℓ' hx
  beta_reduce at hi
  have hc : ∀ i, ((L - 1 - ℓ i : ℕ) : ℝ) = (L : ℝ) - 1 - ℓ i := by
    intro i
    have := hℓlt i
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  have e2 : ∑ i, ((L - 1 - ℓ i : ℕ) : ℝ) * (x i : ℝ) =
      ((L : ℝ) - 1) * ∑ i, (x i : ℝ) - ∑ i, (ℓ i : ℝ) * (x i : ℝ) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [hc i]
    ring
  have e3 : ∑ i, (((ℓ i : ℝ) - ((L : ℝ) - 1) / 2) * (x i : ℝ)) =
      ∑ i, (ℓ i : ℝ) * (x i : ℝ) - ((L : ℝ) - 1) / 2 * ∑ i, (x i : ℝ) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [e2] at hi
  rw [e3, abs_le]
  constructor <;> linarith

lemma abs_exp_sub_one_le (y : ℝ) : |Real.exp y - 1| ≤ |y| * Real.exp |y| := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg (by linarith [Real.add_one_le_exp y]), abs_of_nonneg hy]
    have h1 := Real.add_one_le_exp (-y)
    have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos y, mul_le_mul_of_nonneg_right h1 (Real.exp_pos y).le]
  · rw [abs_of_nonpos (by linarith [Real.exp_le_one_iff.mpr hy]), abs_of_nonpos hy]
    have h1 := Real.add_one_le_exp y
    have h2 : 1 ≤ Real.exp (-y) := Real.one_le_exp (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h2 (neg_nonneg.mpr hy)]

lemma theta_le (L T b3 : ℕ) (Λ : ℝ) (hΛ : Λ ≠ 0) (hb3 : 0 < b3) (hL : 0 < L) (hT : 0 < T)
    (p q : ℕ × ℕ × ℕ) (hp : p.2.2 < L) (hq : q.2.2 < T) :
    |BB6Psi.theta L T b3 Λ p q| ≤ 1 := by
  have hb3r : (0:ℝ) < b3 := by exact_mod_cast hb3
  have hLr : (0:ℝ) < L := by exact_mod_cast hL
  have hTr : (0:ℝ) < T := by exact_mod_cast hT
  have hΛa : 0 < |Λ| := abs_pos.mpr hΛ
  set X : ℝ := (L : ℝ) * T * |Λ| / (2 * b3) with hX
  have hX0 : 0 ≤ X := by positivity
  have hLp : BB6Kit.lamPrime L T b3 Λ = X * Real.exp X := by
    unfold BB6Kit.lamPrime
    rw [hX]
    ring
  have hLpos : 0 < X * Real.exp X := by
    have : 0 < X := by positivity
    positivity
  unfold BB6Psi.theta
  rw [hLp, abs_div, abs_of_pos hLpos, div_le_one hLpos]
  have hlam : |BB6Psi.lam L p| ≤ (L : ℝ) / 2 := by
    unfold BB6Psi.lam
    have h1 : (p.2.2 : ℝ) ≤ (L : ℝ) - 1 := by
      have : p.2.2 + 1 ≤ L := hp
      have : ((p.2.2 + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast this
      push_cast at this
      linarith
    have h2 : (0:ℝ) ≤ p.2.2 := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> linarith
  have htq : (q.2.2 : ℝ) ≤ T := by exact_mod_cast hq.le
  have h4 : (L : ℝ) * T * |Λ| / (2 * b3) * b3 = (L : ℝ) / 2 * T * |Λ| := by
    field_simp
    try ring
  have hy : |-(BB6Psi.lam L p * (q.2.2 : ℝ) * Λ / (b3 : ℝ))| ≤ X := by
    rw [abs_neg, abs_div, abs_mul, abs_mul, abs_of_pos hb3r, abs_of_nonneg (show (0:ℝ) ≤ (q.2.2 : ℝ) from Nat.cast_nonneg _), hX,
      div_le_iff₀ hb3r, h4]
    have : |BB6Psi.lam L p| * (q.2.2 : ℝ) ≤ (L : ℝ) / 2 * T :=
      mul_le_mul hlam htq (Nat.cast_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  calc |Real.exp (-(BB6Psi.lam L p * (q.2.2 : ℝ) * Λ / (b3 : ℝ))) - 1|
      ≤ |-(BB6Psi.lam L p * (q.2.2 : ℝ) * Λ / (b3 : ℝ))| *
          Real.exp |-(BB6Psi.lam L p * (q.2.2 : ℝ) * Λ / (b3 : ℝ))| := abs_exp_sub_one_le _
    _ ≤ X * Real.exp X := mul_le_mul hy (Real.exp_le_exp.mpr hy) (Real.exp_pos _).le hX0

lemma det_norm_le {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (F : Fin N → Fin N → ℝ)
    (hF : ∀ i j, ‖M i j‖ ≤ F i j) (U : ℝ) (hU : ∀ σ : Equiv.Perm (Fin N), ∏ i, F i (σ i) ≤ U) :
    ‖M.det‖ ≤ (N.factorial : ℝ) * U := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ σ : Equiv.Perm (Fin N), ‖Equiv.Perm.sign σ • ∏ i, M.transpose (σ i) i‖ ≤ U := by
    intro σ
    rw [Units.smul_def, zsmul_eq_mul, norm_mul]
    have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
    rw [hs, one_mul, norm_prod]
    refine le_trans (prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)) (hU σ)
    exact hF i (σ i)
  calc ∑ σ : Equiv.Perm (Fin N), ‖Equiv.Perm.sign σ • ∏ i, M.transpose (σ i) i‖
      ≤ ∑ _σ : Equiv.Perm (Fin N), U := sum_le_sum (fun σ _ => h σ)
    _ = (N.factorial : ℝ) * U := by
        rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

lemma phi_norm (c2 c4 α1 α2 L : ℕ) (p : ℕ × ℕ × ℕ) (x : ℂ) (η ζ η0 ζ0 ρ : ℝ) (hx : ‖x‖ = ρ)
    (hρ : 0 ≤ ρ) (hη : |η| ≤ η0) (hζ : |ζ| ≤ ζ0) :
    ‖BB6Psi.phi c2 c4 α1 α2 L p (x * (η : ℂ)) (x * (ζ : ℂ))‖ ≤
      (c2 : ℝ) ^ p.1 * (c4 : ℝ) ^ p.2.1 / ((p.1.factorial : ℝ) * (p.2.1.factorial : ℝ)) *
        (ρ * η0) ^ p.1 * (ρ * ζ0) ^ p.2.1 *
        Real.exp (BB6Psi.lam L p * (η * Real.log (α1 : ℝ) + ζ * Real.log (α2 : ℝ)) * x.re) := by
  unfold BB6Psi.phi
  have hlead : ((c2 : ℂ) ^ p.1 * (c4 : ℂ) ^ p.2.1 / ((p.1.factorial : ℂ) * (p.2.1.factorial : ℂ))) =
      (((c2 : ℝ) ^ p.1 * (c4 : ℝ) ^ p.2.1 / ((p.1.factorial : ℝ) * (p.2.1.factorial : ℝ)) : ℝ) : ℂ) := by
    push_cast
    try ring
  have hexp : ((BB6Psi.lam L p : ℂ) * (x * (η : ℂ) * (Real.log (α1 : ℝ) : ℂ) + x * (ζ : ℂ) * (Real.log (α2 : ℝ) : ℂ))).re =
      BB6Psi.lam L p * (η * Real.log (α1 : ℝ) + ζ * Real.log (α2 : ℝ)) * x.re := by
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
    ring
  have hl : 0 ≤ (c2 : ℝ) ^ p.1 * (c4 : ℝ) ^ p.2.1 / ((p.1.factorial : ℝ) * (p.2.1.factorial : ℝ)) := by positivity
  have he := Real.exp_pos (BB6Psi.lam L p * (η * Real.log (α1 : ℝ) + ζ * Real.log (α2 : ℝ)) * x.re)
  rw [hlead, norm_mul, norm_mul, norm_mul, Complex.norm_exp, hexp, norm_pow, norm_pow, norm_mul, norm_mul, hx]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg hl]
  have h1 : (ρ * |η|) ^ p.1 ≤ (ρ * η0) ^ p.1 :=
    pow_le_pow_left₀ (mul_nonneg hρ (abs_nonneg _)) (mul_le_mul_of_nonneg_left hη hρ) _
  have h2 : (ρ * |ζ|) ^ p.2.1 ≤ (ρ * ζ0) ^ p.2.1 :=
    pow_le_pow_left₀ (mul_nonneg hρ (abs_nonneg _)) (mul_le_mul_of_nonneg_left hζ hρ) _
  apply mul_le_mul_of_nonneg_right _ he.le
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hl) h2 (pow_nonneg (mul_nonneg hρ (abs_nonneg _)) _)
    (mul_nonneg hl (pow_nonneg (mul_nonneg hρ (le_trans (abs_nonneg _) hη)) _))

end MX

set_option maxHeartbeats 2000000 in
theorem solution (K L R S T N b1 b2 b3 α1 α2 α3 : ℕ) (ρ : ℝ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0)
    (kml rst : Fin N → ℕ × ℕ × ℕ) (hrows : BB6Kit.RowsOK K L N kml) (hcols : BB6Kit.ColsOK R S T N rst) (hρ : 0 ≤ ρ) :
    ∀ (I : Finset (Fin N)) (x : ℂ), ‖x‖ = ρ →
      ‖BB6Psi.psi N L R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) b3 α1 α2 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) kml rst I x‖ ≤
      ((N.factorial : ℝ) * (∏ i, (((b3 / Nat.gcd b1 b3 : ℕ) : ℝ) ^ (kml i).1 * ((b3 / Nat.gcd b2 b3 : ℕ) : ℝ) ^ (kml i).2.1 / (((kml i).1.factorial : ℝ) * ((kml i).2.1.factorial : ℝ)))) * (ρ * (((R : ℝ) - 1) / 2 + ((b1 / Nat.gcd b1 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b1 b3 : ℕ) : ℝ) * (((T : ℝ) - 1) / 2))) ^ (∑ i, (kml i).1) * (ρ * (((S : ℝ) - 1) / 2 + ((b2 / Nat.gcd b2 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b2 b3 : ℕ) : ℝ) * (((T : ℝ) - 1) / 2))) ^ (∑ i, (kml i).2.1) *
        Real.exp (ρ * (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) +
          BB6Kit.GK N L R S T T * (Real.log (α3 : ℝ) + |((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ))| / (b3 : ℝ))))) := by
  intro I x hx
  -- reduced coefficients
  have hg13 : 0 < Nat.gcd b1 b3 := Nat.gcd_pos_of_pos_right _ hb3
  have hg23 : 0 < Nat.gcd b2 b3 := Nat.gcd_pos_of_pos_right _ hb3
  have hc2 : 0 < b3 / Nat.gcd b1 b3 := Nat.div_pos (Nat.gcd_le_right _ hb3) hg13
  have hc4 : 0 < b3 / Nat.gcd b2 b3 := Nat.div_pos (Nat.gcd_le_right _ hb3) hg23
  have hb3r : (0 : ℝ) < b3 := by exact_mod_cast hb3
  have hβ1 : ((b1 / Nat.gcd b1 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b1 b3 : ℕ) : ℝ) = (b1 : ℝ) / b3 := by
    have hg : ((Nat.gcd b1 b3 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hg13.ne'
    rw [Nat.cast_div (Nat.gcd_dvd_left b1 b3) hg, Nat.cast_div (Nat.gcd_dvd_right b1 b3) hg]
    first
    | (field_simp; ring)
    | field_simp
  have hβ2 : ((b2 / Nat.gcd b2 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b2 b3 : ℕ) : ℝ) = (b2 : ℝ) / b3 := by
    have hg : ((Nat.gcd b2 b3 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hg23.ne'
    rw [Nat.cast_div (Nat.gcd_dvd_left b2 b3) hg, Nat.cast_div (Nat.gcd_dvd_right b2 b3) hg]
    first
    | (field_simp; ring)
    | field_simp
  generalize b1 / Nat.gcd b1 b3 = c1 at hβ1 ⊢
  generalize b3 / Nat.gcd b1 b3 = c2 at hβ1 hc2 ⊢
  generalize b2 / Nat.gcd b2 b3 = c3 at hβ2 ⊢
  generalize b3 / Nat.gcd b2 b3 = c4 at hβ2 hc4 ⊢
  generalize hΛdef : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) = Λ at hΛ ⊢
  have hc2r : (0 : ℝ) < c2 := by exact_mod_cast hc2
  have hc4r : (0 : ℝ) < c4 := by exact_mod_cast hc4
  have hβ1n : (0 : ℝ) ≤ (c1 : ℝ) / c2 := by positivity
  have hβ2n : (0 : ℝ) ≤ (c3 : ℝ) / c4 := by positivity
  -- basic sizes
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
  have ha1 : 0 ≤ Real.log (α1 : ℝ) := Real.log_nonneg (by exact_mod_cast hα1.le)
  have ha2 : 0 ≤ Real.log (α2 : ℝ) := Real.log_nonneg (by exact_mod_cast hα2.le)
  -- rows and columns
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
    linarith [e1, e2, MX.rowsum K L f]
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
  have hℓlt : ∀ i, (kml i).2.2 < L := by
    intro i
    have := hrows.2 i
    unfold BB6Kit.rowSet at this
    simp only [mem_filter, mem_product, mem_range] at this
    exact this.1.2.2
  -- Σ λ_i = 0
  have hKr' := hKr
  have hcardR : ((BB6Kit.rowSet K L).card : ℝ) = N := by
    rw [hNA]
    have := MX.rowsum K L (fun _ => (1:ℝ))
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at this
    exact this
  have hcard : (BB6Kit.rowSet K L).card = N := by exact_mod_cast hcardR
  have himg : univ.image kml = BB6Kit.rowSet K L := by
    apply eq_of_subset_of_card_le
    · intro p hp
      rw [mem_image] at hp
      obtain ⟨i, _, rfl⟩ := hp
      exact hrows.2 i
    · rw [card_image_of_injective _ hrows.1, card_univ, Fintype.card_fin, hcard]
  have hsumℓ : ∑ i, BB6Psi.lam L (kml i) = 0 := by
    have e : ∑ i, ((kml i).2.2 : ℝ) = ∑ p ∈ BB6Kit.rowSet K L, (p.2.2 : ℝ) := by
      rw [← himg, sum_image (by intro x _ y _ h; exact hrows.1 h)]
    unfold BB6Psi.lam
    rw [sum_sub_distrib, e, MX.rowsum K L (fun v => (v : ℝ)), MX.gauss, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, hNA]
    ring
  -- rearrangement for each column coordinate and each permutation
  have hr : ∀ σ : Equiv.Perm (Fin N), |∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).1 : ℝ)| ≤ BB6Kit.GK N L R S T R := by
    intro σ
    have h := MX.rearr_abs N L R _ ((S:ℝ) * T) hNpos hA (mul_pos hSr hTr) hNA hNX1
      (fun i => (kml i).2.2) (fun i => (rst (σ i)).1) hℓlt hrow
      (fun f hf => (Equiv.sum_comp σ (fun j => f ((rst j).1))).trans_le (hcol1 f hf))
    have hG : BB6Kit.GK N L R S T R = (N:ℝ) * L * R * (1 / 4 - N / (12 * (R * ((S:ℝ) * T)))) / 2 := by
      unfold BB6Kit.GK BB6Kit.gK; ring
    rw [hG]
    exact h
  have hs : ∀ σ : Equiv.Perm (Fin N), |∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).2.1 : ℝ)| ≤ BB6Kit.GK N L R S T S := by
    intro σ
    have h := MX.rearr_abs N L S _ ((R:ℝ) * T) hNpos hA (mul_pos hRr hTr) hNA hNX2
      (fun i => (kml i).2.2) (fun i => (rst (σ i)).2.1) hℓlt hrow
      (fun f hf => (Equiv.sum_comp σ (fun j => f ((rst j).2.1))).trans_le (hcol2 f hf))
    have hG : BB6Kit.GK N L R S T S = (N:ℝ) * L * S * (1 / 4 - N / (12 * (S * ((R:ℝ) * T)))) / 2 := by
      unfold BB6Kit.GK BB6Kit.gK; ring
    rw [hG]
    exact h
  have ht : ∀ σ : Equiv.Perm (Fin N), |∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).2.2 : ℝ)| ≤ BB6Kit.GK N L R S T T := by
    intro σ
    have h := MX.rearr_abs N L T _ ((R:ℝ) * S) hNpos hA (mul_pos hRr hSr) hNA hNX3
      (fun i => (kml i).2.2) (fun i => (rst (σ i)).2.2) hℓlt hrow
      (fun f hf => (Equiv.sum_comp σ (fun j => f ((rst j).2.2))).trans_le (hcol3 f hf))
    have hG : BB6Kit.GK N L R S T T = (N:ℝ) * L * T * (1 / 4 - N / (12 * (T * ((R:ℝ) * S)))) / 2 := by
      unfold BB6Kit.GK BB6Kit.gK; ring
    rw [hG]
    exact h
  -- eta and zeta sums
  have hη : ∀ σ : Equiv.Perm (Fin N), |∑ i, BB6Psi.lam L (kml i) * BB6Psi.eta R T c1 c2 (rst (σ i))| ≤
      BB6Kit.GK N L R S T R + (c1 : ℝ) / c2 * BB6Kit.GK N L R S T T := by
    intro σ
    have e : ∑ i, BB6Psi.lam L (kml i) * BB6Psi.eta R T c1 c2 (rst (σ i)) =
        ∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).1 : ℝ) +
          (c1 : ℝ) / c2 * ∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).2.2 : ℝ) -
          (((R : ℝ) - 1) / 2 + (c1 : ℝ) / c2 * (((T : ℝ) - 1) / 2)) * ∑ i, BB6Psi.lam L (kml i) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      apply sum_congr rfl
      intro i _
      unfold BB6Psi.eta
      ring
    rw [e, hsumℓ, mul_zero, sub_zero]
    calc |∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).1 : ℝ) +
          (c1 : ℝ) / c2 * ∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).2.2 : ℝ)|
        ≤ |∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).1 : ℝ)| +
          |(c1 : ℝ) / c2 * ∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).2.2 : ℝ)| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg hβ1n]
        exact add_le_add (hr σ) (mul_le_mul_of_nonneg_left (ht σ) hβ1n)
  have hζ : ∀ σ : Equiv.Perm (Fin N), |∑ i, BB6Psi.lam L (kml i) * BB6Psi.zeta S T c3 c4 (rst (σ i))| ≤
      BB6Kit.GK N L R S T S + (c3 : ℝ) / c4 * BB6Kit.GK N L R S T T := by
    intro σ
    have e : ∑ i, BB6Psi.lam L (kml i) * BB6Psi.zeta S T c3 c4 (rst (σ i)) =
        ∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).2.1 : ℝ) +
          (c3 : ℝ) / c4 * ∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).2.2 : ℝ) -
          (((S : ℝ) - 1) / 2 + (c3 : ℝ) / c4 * (((T : ℝ) - 1) / 2)) * ∑ i, BB6Psi.lam L (kml i) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      apply sum_congr rfl
      intro i _
      unfold BB6Psi.zeta
      ring
    rw [e, hsumℓ, mul_zero, sub_zero]
    calc |∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).2.1 : ℝ) +
          (c3 : ℝ) / c4 * ∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).2.2 : ℝ)|
        ≤ |∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).2.1 : ℝ)| +
          |(c3 : ℝ) / c4 * ∑ i, BB6Psi.lam L (kml i) * ((rst (σ i)).2.2 : ℝ)| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg hβ2n]
        exact add_le_add (hs σ) (mul_le_mul_of_nonneg_left (ht σ) hβ2n)
  -- entry bounds
  have hηb : ∀ j, |BB6Psi.eta R T c1 c2 (rst j)| ≤ ((R : ℝ) - 1) / 2 + (c1 : ℝ) / c2 * (((T : ℝ) - 1) / 2) := by
    intro j
    obtain ⟨h1, _, h3⟩ := hcols.2 j
    have h1' : ((rst j).1 : ℝ) ≤ (R : ℝ) - 1 := by
      have : (((rst j).1 + 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast h1
      push_cast at this; linarith
    have h3' : ((rst j).2.2 : ℝ) ≤ (T : ℝ) - 1 := by
      have : (((rst j).2.2 + 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast h3
      push_cast at this; linarith
    have h0 : (0 : ℝ) ≤ (rst j).1 := Nat.cast_nonneg _
    have h0' : (0 : ℝ) ≤ (rst j).2.2 := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left h3' hβ1n
    have hm0 := mul_nonneg hβ1n h0'
    unfold BB6Psi.eta
    rw [abs_le]
    constructor <;> linarith
  have hζb : ∀ j, |BB6Psi.zeta S T c3 c4 (rst j)| ≤ ((S : ℝ) - 1) / 2 + (c3 : ℝ) / c4 * (((T : ℝ) - 1) / 2) := by
    intro j
    obtain ⟨_, h2, h3⟩ := hcols.2 j
    have h2' : ((rst j).2.1 : ℝ) ≤ (S : ℝ) - 1 := by
      have : (((rst j).2.1 + 1 : ℕ) : ℝ) ≤ S := by exact_mod_cast h2
      push_cast at this; linarith
    have h3' : ((rst j).2.2 : ℝ) ≤ (T : ℝ) - 1 := by
      have : (((rst j).2.2 + 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast h3
      push_cast at this; linarith
    have h0 : (0 : ℝ) ≤ (rst j).2.1 := Nat.cast_nonneg _
    have h0' : (0 : ℝ) ≤ (rst j).2.2 := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left h3' hβ2n
    have hm0 := mul_nonneg hβ2n h0'
    unfold BB6Psi.zeta
    rw [abs_le]
    constructor <;> linarith
  -- the main estimate
  obtain ⟨η0, hη0⟩ : ∃ η0 : ℝ, η0 = ((R : ℝ) - 1) / 2 + (c1 : ℝ) / c2 * (((T : ℝ) - 1) / 2) := ⟨_, rfl⟩
  obtain ⟨ζ0, hζ0⟩ : ∃ ζ0 : ℝ, ζ0 = ((S : ℝ) - 1) / 2 + (c3 : ℝ) / c4 * (((T : ℝ) - 1) / 2) := ⟨_, rfl⟩
  rw [← hη0, ← hζ0]
  rw [← hη0] at hηb
  rw [← hζ0] at hζb
  have hη0n : 0 ≤ η0 := le_trans (abs_nonneg _) (hηb ⟨0, hNpos⟩)
  have hζ0n : 0 ≤ ζ0 := le_trans (abs_nonneg _) (hζb ⟨0, hNpos⟩)
  obtain ⟨F, hF⟩ : ∃ F : Fin N → Fin N → ℝ, F = fun i j =>
      (c2 : ℝ) ^ (kml i).1 * (c4 : ℝ) ^ (kml i).2.1 / (((kml i).1.factorial : ℝ) * ((kml i).2.1.factorial : ℝ)) *
        (ρ * η0) ^ (kml i).1 * (ρ * ζ0) ^ (kml i).2.1 *
        Real.exp (BB6Psi.lam L (kml i) * (BB6Psi.eta R T c1 c2 (rst j) * Real.log (α1 : ℝ) +
          BB6Psi.zeta S T c3 c4 (rst j) * Real.log (α2 : ℝ)) * x.re) := ⟨_, rfl⟩
  unfold BB6Psi.psi
  refine le_trans (MX.det_norm_le _ F ?_ ((∏ i, ((c2 : ℝ) ^ (kml i).1 * (c4 : ℝ) ^ (kml i).2.1 /
      (((kml i).1.factorial : ℝ) * ((kml i).2.1.factorial : ℝ)))) * (ρ * η0) ^ (∑ i, (kml i).1) *
      (ρ * ζ0) ^ (∑ i, (kml i).2.1) *
      Real.exp (ρ * (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) +
        BB6Kit.GK N L R S T T * (Real.log (α3 : ℝ) + |Λ| / (b3 : ℝ))))) ?_) (le_of_eq (by ring))
  · -- entrywise bound
    intro i j
    simp only [Matrix.of_apply]
    rw [norm_mul]
    have hc : ‖(if i ∈ I then (1 : ℂ) else (BB6Psi.theta L T b3 Λ (kml i) (rst j) : ℂ))‖ ≤ 1 := by
      split_ifs
      · simp
      · rw [Complex.norm_real, Real.norm_eq_abs]
        exact MX.theta_le L T b3 Λ hΛ hb3 (by omega) hT (kml i) (rst j) (hℓlt i) (hcols.2 j).2.2
    have hp := MX.phi_norm c2 c4 α1 α2 L (kml i) x (BB6Psi.eta R T c1 c2 (rst j)) (BB6Psi.zeta S T c3 c4 (rst j))
      η0 ζ0 ρ hx hρ (hηb j) (hζb j)
    rw [hF]
    calc ‖(if i ∈ I then (1 : ℂ) else (BB6Psi.theta L T b3 Λ (kml i) (rst j) : ℂ))‖ *
          ‖BB6Psi.phi c2 c4 α1 α2 L (kml i) (x * (BB6Psi.eta R T c1 c2 (rst j) : ℂ)) (x * (BB6Psi.zeta S T c3 c4 (rst j) : ℂ))‖
        ≤ 1 * ‖BB6Psi.phi c2 c4 α1 α2 L (kml i) (x * (BB6Psi.eta R T c1 c2 (rst j) : ℂ)) (x * (BB6Psi.zeta S T c3 c4 (rst j) : ℂ))‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hp
  · -- product over a permutation
    intro σ
    rw [hF]
    simp only
    rw [prod_mul_distrib, prod_mul_distrib, prod_mul_distrib, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, ← Real.exp_sum]
    have hlead : 0 ≤ ∏ i, ((c2 : ℝ) ^ (kml i).1 * (c4 : ℝ) ^ (kml i).2.1 /
        (((kml i).1.factorial : ℝ) * ((kml i).2.1.factorial : ℝ))) := by
      apply prod_nonneg; intro i _; positivity
    have hpow : 0 ≤ (ρ * η0) ^ (∑ i, (kml i).1) * (ρ * ζ0) ^ (∑ i, (kml i).2.1) :=
      mul_nonneg (pow_nonneg (mul_nonneg hρ hη0n) _) (pow_nonneg (mul_nonneg hρ hζ0n) _)
    have hexp : ∑ i, BB6Psi.lam L (kml i) * (BB6Psi.eta R T c1 c2 (rst (σ i)) * Real.log (α1 : ℝ) +
          BB6Psi.zeta S T c3 c4 (rst (σ i)) * Real.log (α2 : ℝ)) * x.re ≤
        ρ * (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) +
          BB6Kit.GK N L R S T T * (Real.log (α3 : ℝ) + |Λ| / (b3 : ℝ))) := by
      have e : ∑ i, BB6Psi.lam L (kml i) * (BB6Psi.eta R T c1 c2 (rst (σ i)) * Real.log (α1 : ℝ) +
            BB6Psi.zeta S T c3 c4 (rst (σ i)) * Real.log (α2 : ℝ)) * x.re =
          x.re * (Real.log (α1 : ℝ) * ∑ i, BB6Psi.lam L (kml i) * BB6Psi.eta R T c1 c2 (rst (σ i)) +
            Real.log (α2 : ℝ) * ∑ i, BB6Psi.lam L (kml i) * BB6Psi.zeta S T c3 c4 (rst (σ i))) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib, mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      rw [e]
      set S1 := ∑ i, BB6Psi.lam L (kml i) * BB6Psi.eta R T c1 c2 (rst (σ i))
      set S2 := ∑ i, BB6Psi.lam L (kml i) * BB6Psi.zeta S T c3 c4 (rst (σ i))
      have hre : |x.re| ≤ ρ := by rw [← hx]; exact Complex.abs_re_le_norm x
      have hT1 : |Real.log (α1 : ℝ) * S1 + Real.log (α2 : ℝ) * S2| ≤
          Real.log (α1 : ℝ) * (BB6Kit.GK N L R S T R + (c1 : ℝ) / c2 * BB6Kit.GK N L R S T T) +
          Real.log (α2 : ℝ) * (BB6Kit.GK N L R S T S + (c3 : ℝ) / c4 * BB6Kit.GK N L R S T T) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg ha1, abs_of_nonneg ha2]
        exact add_le_add (mul_le_mul_of_nonneg_left (hη σ) ha1) (mul_le_mul_of_nonneg_left (hζ σ) ha2)
      have hG3 : 0 ≤ BB6Kit.GK N L R S T T := by
        unfold BB6Kit.GK BB6Kit.gK
        have h12 : (N:ℝ) / (12 * (R:ℝ) * S * T) ≤ 1 / 12 := by
          rw [div_le_iff₀ (by positivity)]
          linarith
        have : 0 ≤ (1:ℝ) / 4 - (N:ℝ) / (12 * (R:ℝ) * S * T) := by linarith
        exact div_nonneg (mul_nonneg (by positivity) this) (by norm_num)
      have hβ : (c1 : ℝ) / c2 * Real.log (α1 : ℝ) + (c3 : ℝ) / c4 * Real.log (α2 : ℝ) =
          Real.log (α3 : ℝ) + Λ / (b3 : ℝ) := by
        have hb3ne : (b3 : ℝ) ≠ 0 := hb3r.ne'
        rw [hβ1, hβ2, ← hΛdef]
        field_simp
        try ring
      have hΛb : Λ / (b3 : ℝ) ≤ |Λ| / (b3 : ℝ) := div_le_div_of_nonneg_right (le_abs_self Λ) hb3r.le
      have hfin : Real.log (α1 : ℝ) * (BB6Kit.GK N L R S T R + (c1 : ℝ) / c2 * BB6Kit.GK N L R S T T) +
          Real.log (α2 : ℝ) * (BB6Kit.GK N L R S T S + (c3 : ℝ) / c4 * BB6Kit.GK N L R S T T) ≤
          BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) +
            BB6Kit.GK N L R S T T * (Real.log (α3 : ℝ) + |Λ| / (b3 : ℝ)) := by
        have h1 : Real.log (α1 : ℝ) * (BB6Kit.GK N L R S T R + (c1 : ℝ) / c2 * BB6Kit.GK N L R S T T) +
            Real.log (α2 : ℝ) * (BB6Kit.GK N L R S T S + (c3 : ℝ) / c4 * BB6Kit.GK N L R S T T) =
            BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) +
              BB6Kit.GK N L R S T T * ((c1 : ℝ) / c2 * Real.log (α1 : ℝ) + (c3 : ℝ) / c4 * Real.log (α2 : ℝ)) := by
          ring
        rw [h1, hβ]
        have := mul_le_mul_of_nonneg_left hΛb hG3
        linarith
      calc x.re * (Real.log (α1 : ℝ) * S1 + Real.log (α2 : ℝ) * S2)
          ≤ |x.re * (Real.log (α1 : ℝ) * S1 + Real.log (α2 : ℝ) * S2)| := le_abs_self _
        _ = |x.re| * |Real.log (α1 : ℝ) * S1 + Real.log (α2 : ℝ) * S2| := abs_mul _ _
        _ ≤ ρ * (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) +
              BB6Kit.GK N L R S T T * (Real.log (α3 : ℝ) + |Λ| / (b3 : ℝ))) :=
            mul_le_mul hre (hT1.trans hfin) (abs_nonneg _) hρ
    have hE := Real.exp_le_exp.mpr hexp
    calc (∏ i, ((c2 : ℝ) ^ (kml i).1 * (c4 : ℝ) ^ (kml i).2.1 /
            (((kml i).1.factorial : ℝ) * ((kml i).2.1.factorial : ℝ)))) * (ρ * η0) ^ (∑ i, (kml i).1) *
          (ρ * ζ0) ^ (∑ i, (kml i).2.1) *
          Real.exp (∑ i, BB6Psi.lam L (kml i) * (BB6Psi.eta R T c1 c2 (rst (σ i)) * Real.log (α1 : ℝ) +
            BB6Psi.zeta S T c3 c4 (rst (σ i)) * Real.log (α2 : ℝ)) * x.re)
        ≤ (∏ i, ((c2 : ℝ) ^ (kml i).1 * (c4 : ℝ) ^ (kml i).2.1 /
            (((kml i).1.factorial : ℝ) * ((kml i).2.1.factorial : ℝ)))) * (ρ * η0) ^ (∑ i, (kml i).1) *
          (ρ * ζ0) ^ (∑ i, (kml i).2.1) *
          Real.exp (ρ * (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) +
            BB6Kit.GK N L R S T T * (Real.log (α3 : ℝ) + |Λ| / (b3 : ℝ)))) := by
          apply mul_le_mul_of_nonneg_left hE
          exact mul_nonneg (mul_nonneg hlead (pow_nonneg (mul_nonneg hρ hη0n) _)) (pow_nonneg (mul_nonneg hρ hζ0n) _)
      _ = _ := rfl
