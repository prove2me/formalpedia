-- Prove2me | solution 1 for BinaryThreeLCC.JM.poincare_of_cut_dense
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:05:42.29725+00:00
-- url     : https://prove2.me/submissions/95c23535-0092-462b-b3db-26fd2c91b7b9

import Mathlib

set_option autoImplicit false

namespace BinaryThreeLCC.JM

namespace T56aux

open Finset

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

noncomputable def ind (S : Finset Ω) (i : Ω) : ℝ := if i ∈ S then 1 else 0

lemma sum_abs_ind (F : Ω → Ω → ℝ) (S : Finset Ω) :
    ∑ i, ∑ j, F i j * |ind S i - ind S j| =
      ∑ i ∈ S, ∑ j ∈ univ \ S, F i j + ∑ i ∈ univ \ S, ∑ j ∈ S, F i j := by
  have hsplit : ∀ g : Ω → ℝ, ∑ j, g j = ∑ j ∈ S, g j + ∑ j ∈ univ \ S, g j := by
    intro g; rw [add_comm, Finset.sum_sdiff (Finset.subset_univ S)]
  rw [hsplit]
  congr 1
  · apply Finset.sum_congr rfl; intro i hi
    rw [hsplit]
    have h1 : ∑ j ∈ S, F i j * |ind S i - ind S j| = 0 := by
      apply Finset.sum_eq_zero; intro j hj; simp [ind, hi, hj]
    have h2 : ∑ j ∈ univ \ S, F i j * |ind S i - ind S j| = ∑ j ∈ univ \ S, F i j := by
      apply Finset.sum_congr rfl; intro j hj
      have : j ∉ S := (Finset.mem_sdiff.1 hj).2
      simp [ind, hi, this]
    rw [h1, h2, zero_add]
  · apply Finset.sum_congr rfl; intro i hi
    have hi' : i ∉ S := (Finset.mem_sdiff.1 hi).2
    rw [hsplit]
    have h1 : ∑ j ∈ S, F i j * |ind S i - ind S j| = ∑ j ∈ S, F i j := by
      apply Finset.sum_congr rfl; intro j hj; simp [ind, hi', hj]
    have h2 : ∑ j ∈ univ \ S, F i j * |ind S i - ind S j| = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      have : j ∉ S := (Finset.mem_sdiff.1 hj).2
      simp [ind, hi', this]
    rw [h1, h2, add_zero]

lemma cut_ind (wt : Ω → Ω → ℝ) (κ : ℝ)
    (hcut : ∀ S : Finset Ω, κ * S.card * (Finset.univ \ S).card ≤
      ∑ i ∈ S, ∑ j ∈ Finset.univ \ S, wt i j) (S : Finset Ω) :
    κ * ∑ i, ∑ j, |ind S i - ind S j| ≤ ∑ i, ∑ j, wt i j * |ind S i - ind S j| := by
  have e1 := sum_abs_ind (fun _ _ => (1:ℝ)) S
  simp only [one_mul] at e1
  rw [e1, sum_abs_ind]
  have h1 := hcut S
  have h2 := hcut (univ \ S)
  rw [Finset.sdiff_sdiff_eq_self (subset_univ S)] at h2
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  nlinarith

lemma level_split (a b t0 t1 : ℝ) (h01 : t0 < t1) (ha : a = t0 ∨ t1 ≤ a)
    (hb : b = t0 ∨ t1 ≤ b) :
    |a - b| = |max a t1 - max b t1| +
      (t1 - t0) * |(if a < t1 then (1:ℝ) else 0) - (if b < t1 then 1 else 0)| := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [ha, hb]; simp
  · rw [ha, if_pos h01, if_neg (not_lt.mpr hb), max_eq_right h01.le, max_eq_left hb]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
      show (1:ℝ) - 0 = 1 by norm_num, abs_one]
    ring
  · rw [hb, if_neg (not_lt.mpr ha), if_pos h01, max_eq_left ha, max_eq_right h01.le]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
      show (0:ℝ) - 1 = -1 by norm_num, abs_neg, abs_one]
    ring
  · rw [if_neg (not_lt.mpr ha), if_neg (not_lt.mpr hb), max_eq_left ha, max_eq_left hb]
    simp

lemma l1 (wt : Ω → Ω → ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hcut : ∀ S : Finset Ω, κ * S.card * (Finset.univ \ S).card ≤
      ∑ i ∈ S, ∑ j ∈ Finset.univ \ S, wt i j) :
    ∀ (n : ℕ) (y : Ω → ℝ), (univ.image y).card ≤ n →
      κ * ∑ i, ∑ j, |y i - y j| ≤ ∑ i, ∑ j, wt i j * |y i - y j| := by
  intro n
  induction n with
  | zero =>
    intro y hy
    have h0 : univ.image y = ∅ := card_eq_zero.mp (Nat.le_zero.mp hy)
    have hu : (univ : Finset Ω) = ∅ := by simpa using h0
    simp [hu]
  | succ n ih =>
    intro y hy
    by_cases h1 : (univ.image y).card ≤ 1
    · have hall : ∀ i j, y i = y j := by
        intro i j
        exact Finset.card_le_one.mp h1 _ (mem_image_of_mem y (mem_univ i)) _
          (mem_image_of_mem y (mem_univ j))
      have h0 : ∀ i j, |y i - y j| = 0 := by intro i j; rw [hall i j, sub_self, abs_zero]
      simp [h0]
    · push_neg at h1
      set T := univ.image y with hT
      have hTne : T.Nonempty := card_pos.mp (by omega)
      set t0 := T.min' hTne with ht0
      have ht0mem : t0 ∈ T := min'_mem T hTne
      have hT1ne : (T.erase t0).Nonempty := by
        rw [← card_pos, card_erase_of_mem ht0mem]; omega
      set t1 := (T.erase t0).min' hT1ne with ht1
      have ht1mem : t1 ∈ T.erase t0 := min'_mem _ _
      have ht01 : t0 < t1 := lt_of_le_of_ne (min'_le T t1 (mem_of_mem_erase ht1mem))
        (ne_of_mem_erase ht1mem).symm
      have hyc : ∀ i, y i = t0 ∨ t1 ≤ y i := by
        intro i
        by_cases h : y i = t0
        · left; exact h
        · right; exact min'_le _ _ (mem_erase.mpr ⟨h, mem_image_of_mem y (mem_univ i)⟩)
      set y' : Ω → ℝ := fun i => max (y i) t1 with hy'
      set S := univ.filter (fun i => y i < t1) with hS
      have hind : ∀ i, ind S i = if y i < t1 then 1 else 0 := by
        intro i; simp [ind, S]
      have hpt : ∀ i j, |y i - y j| = |y' i - y' j| + (t1 - t0) * |ind S i - ind S j| := by
        intro i j
        rw [hind, hind]
        exact level_split _ _ _ _ ht01 (hyc i) (hyc j)
      have eL : ∑ i, ∑ j, wt i j * |y i - y j| = ∑ i, ∑ j, wt i j * |y' i - y' j| +
          (t1 - t0) * ∑ i, ∑ j, wt i j * |ind S i - ind S j| := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
        rw [hpt i j]; ring
      have eR : ∑ i, ∑ j, |y i - y j| = ∑ i, ∑ j, |y' i - y' j| +
          (t1 - t0) * ∑ i, ∑ j, |ind S i - ind S j| := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
        rw [hpt i j]
      have hsub : univ.image y' ⊆ T.erase t0 := by
        intro x hx
        obtain ⟨i, -, rfl⟩ := mem_image.mp hx
        rcases hyc i with h | h
        · simp only [y']; rw [h, max_eq_right ht01.le]; exact ht1mem
        · simp only [y']; rw [max_eq_left h]
          exact mem_erase.mpr ⟨(lt_of_lt_of_le ht01 h).ne', mem_image_of_mem y (mem_univ i)⟩
      have hcard := card_le_card hsub
      rw [card_erase_of_mem ht0mem] at hcard
      have i1 := ih y' (by omega)
      have i2 := cut_ind wt κ hcut S
      have i3 := mul_le_mul_of_nonneg_left i2 (sub_nonneg.mpr ht01.le)
      rw [eL, eR]
      have : κ * (∑ i, ∑ j, |y' i - y' j| + (t1 - t0) * ∑ i, ∑ j, |ind S i - ind S j|) =
          κ * ∑ i, ∑ j, |y' i - y' j| +
            (t1 - t0) * (κ * ∑ i, ∑ j, |ind S i - ind S j|) := by ring
      rw [this]
      linarith

lemma exists_median (h : Ω → ℝ) : ∃ c : ℝ,
    2 * (univ.filter (fun i => c < h i)).card ≤ Fintype.card Ω ∧
    2 * (univ.filter (fun i => h i < c)).card ≤ Fintype.card Ω := by
  by_cases hne : (univ : Finset Ω).Nonempty
  swap
  · refine ⟨0, ?_, ?_⟩ <;> simp [not_nonempty_iff_eq_empty.mp hne]
  set T := univ.image h
  have hTne : T.Nonempty := hne.image h
  set S' := T.filter (fun t => 2 * (univ.filter (fun i => h i < t)).card ≤ Fintype.card Ω)
  have hS'ne : S'.Nonempty := by
    refine ⟨T.min' hTne, mem_filter.mpr ⟨min'_mem _ _, ?_⟩⟩
    have : (univ.filter (fun i => h i < T.min' hTne)) = ∅ := by
      apply filter_eq_empty_iff.mpr; intro i _
      exact not_lt.mpr (min'_le T _ (mem_image_of_mem h (mem_univ i)))
    rw [this]; simp
  set c := S'.max' hS'ne
  have hcS : c ∈ S' := max'_mem _ _
  refine ⟨c, ?_, (mem_filter.mp hcS).2⟩
  by_contra hbig
  push_neg at hbig
  have hgt_ne : (T.filter (fun t => c < t)).Nonempty := by
    obtain ⟨i, hi⟩ : (univ.filter (fun i => c < h i)).Nonempty := by
      rw [← card_pos]; omega
    exact ⟨h i, mem_filter.mpr ⟨mem_image_of_mem h (mem_univ i), (mem_filter.mp hi).2⟩⟩
  set c' := (T.filter (fun t => c < t)).min' hgt_ne
  have hc'mem : c' ∈ T.filter (fun t => c < t) := min'_mem _ hgt_ne
  have hcc' : c < c' := (mem_filter.mp hc'mem).2
  have hsub : univ.filter (fun i => h i < c') ⊆ univ.filter (fun i => ¬ (c < h i)) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    intro hci
    have : c' ≤ h i := min'_le _ _ (mem_filter.mpr ⟨mem_image_of_mem h (mem_univ i), hci⟩)
    linarith
  have hcount := card_filter_add_card_filter_not (s := (univ : Finset Ω))
    (fun i => c < h i)
  rw [card_univ] at hcount
  have h1 := card_le_card hsub
  have hc'S : c' ∈ S' := mem_filter.mpr ⟨(mem_filter.mp hc'mem).1, by omega⟩
  have : c' ≤ c := le_max' S' c' hc'S
  linarith

lemma pt_posneg (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 + (max (-a) 0 - max (-b) 0) ^ 2 ≤ (a - b) ^ 2 := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_right ha, max_eq_right hb, max_eq_left (neg_nonneg.mpr ha),
      max_eq_left (neg_nonneg.mpr hb)]; nlinarith
  · rw [max_eq_right ha, max_eq_left hb, max_eq_left (neg_nonneg.mpr ha),
      max_eq_right (neg_nonpos.mpr hb)]; nlinarith [mul_nonpos_iff.mpr (Or.inr ⟨ha, hb⟩)]
  · rw [max_eq_left ha, max_eq_right hb, max_eq_right (neg_nonpos.mpr ha),
      max_eq_left (neg_nonneg.mpr hb)]; nlinarith [mul_nonpos_iff.mpr (Or.inl ⟨ha, hb⟩)]
  · rw [max_eq_left ha, max_eq_left hb, max_eq_right (neg_nonpos.mpr ha),
      max_eq_right (neg_nonpos.mpr hb)]; nlinarith

lemma pos_part (wt : Ω → Ω → ℝ) (hw : ∀ i j, 0 ≤ wt i j) (D : ℝ)
    (hrow : ∀ i, ∑ j, wt i j ≤ D) (hcol : ∀ j, ∑ i, wt i j ≤ D)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hcut : ∀ S : Finset Ω, κ * S.card * (Finset.univ \ S).card ≤
      ∑ i ∈ S, ∑ j ∈ Finset.univ \ S, wt i j)
    (f : Ω → ℝ) (hf : ∀ i, 0 ≤ f i) (Z : Finset Ω) (hZ : ∀ i ∈ Z, f i = 0)
    (hZc : (Fintype.card Ω : ℝ) ≤ 2 * Z.card) :
    κ ^ 2 * (Fintype.card Ω : ℝ) ^ 2 / (4 * D) * ∑ i, f i ^ 2 ≤
      ∑ i, ∑ j, wt i j * (f i - f j) ^ 2 := by
  have hA : 0 ≤ ∑ i, f i ^ 2 := sum_nonneg (fun i _ => sq_nonneg _)
  have hDir : 0 ≤ ∑ i, ∑ j, wt i j * (f i - f j) ^ 2 :=
    sum_nonneg (fun i _ => sum_nonneg (fun j _ => mul_nonneg (hw i j) (sq_nonneg _)))
  have hL1 := l1 wt κ hκ hcut _ (fun i => f i ^ 2) le_rfl
  -- pairs lower bound
  have hpt : ∀ i j, ind Z j * f i ^ 2 + ind Z i * f j ^ 2 ≤ |f i ^ 2 - f j ^ 2| := by
    intro i j
    have a1 := le_abs_self (f i ^ 2 - f j ^ 2)
    have a2 := neg_le_abs (f i ^ 2 - f j ^ 2)
    by_cases hi : i ∈ Z <;> by_cases hj : j ∈ Z
    · simp [ind, hi, hj, hZ i hi, hZ j hj]
    · have hfi := hZ i hi
      simp only [ind, hi, hj, if_true, if_false]
      rw [hfi] at a2 ⊢; nlinarith
    · have hfj := hZ j hj
      simp only [ind, hi, hj, if_true, if_false]
      rw [hfj] at a1 ⊢; nlinarith
    · simp only [ind, hi, hj, if_true, if_false]
      nlinarith [abs_nonneg (f i ^ 2 - f j ^ 2)]
  have hindsum : ∑ j, ind Z j = Z.card := by
    simp [ind, Finset.sum_boole]
  have hpairs : 2 * (Z.card : ℝ) * ∑ i, f i ^ 2 ≤ ∑ i, ∑ j, |f i ^ 2 - f j ^ 2| := by
    have eA : ∑ i, ∑ j, ind Z j * f i ^ 2 = Z.card * ∑ i, f i ^ 2 := by
      rw [Finset.mul_sum]; apply sum_congr rfl; intro i _
      rw [← Finset.sum_mul, hindsum]
    have eB : ∑ i, ∑ j, ind Z i * f j ^ 2 = Z.card * ∑ i, f i ^ 2 := by
      rw [Finset.sum_comm]; exact eA
    calc 2 * (Z.card : ℝ) * ∑ i, f i ^ 2
        = ∑ i, ∑ j, (ind Z j * f i ^ 2 + ind Z i * f j ^ 2) := by
          simp only [Finset.sum_add_distrib]; rw [eA, eB]; ring
      _ ≤ _ := sum_le_sum (fun i _ => sum_le_sum (fun j _ => hpt i j))
  -- Cauchy-Schwarz
  have hCS : (∑ i, ∑ j, wt i j * |f i ^ 2 - f j ^ 2|) ^ 2 ≤
      (∑ i, ∑ j, wt i j * (f i - f j) ^ 2) * ∑ i, ∑ j, wt i j * (f i + f j) ^ 2 := by
    have e1 : ∑ i, ∑ j, wt i j * |f i ^ 2 - f j ^ 2| = ∑ x : Ω × Ω,
        (Real.sqrt (wt x.1 x.2) * |f x.1 - f x.2|) *
          (Real.sqrt (wt x.1 x.2) * (f x.1 + f x.2)) := by
      rw [Fintype.sum_prod_type]; dsimp only; apply sum_congr rfl; intro i _
      apply sum_congr rfl; intro j _
      have hw' := Real.mul_self_sqrt (hw i j)
      have : |f i ^ 2 - f j ^ 2| = |f i - f j| * (f i + f j) := by
        rw [show f i ^ 2 - f j ^ 2 = (f i - f j) * (f i + f j) by ring, abs_mul,
          abs_of_nonneg (add_nonneg (hf i) (hf j))]
      rw [this]
      calc wt i j * (|f i - f j| * (f i + f j))
          = (Real.sqrt (wt i j) * Real.sqrt (wt i j)) * (|f i - f j| * (f i + f j)) := by
            rw [hw']
        _ = _ := by ring
    have e2 : ∑ i, ∑ j, wt i j * (f i - f j) ^ 2 =
        ∑ x : Ω × Ω, (Real.sqrt (wt x.1 x.2) * |f x.1 - f x.2|) ^ 2 := by
      rw [Fintype.sum_prod_type]; dsimp only; apply sum_congr rfl; intro i _
      apply sum_congr rfl; intro j _
      rw [mul_pow, Real.sq_sqrt (hw i j), sq_abs]
    have e3 : ∑ i, ∑ j, wt i j * (f i + f j) ^ 2 =
        ∑ x : Ω × Ω, (Real.sqrt (wt x.1 x.2) * (f x.1 + f x.2)) ^ 2 := by
      rw [Fintype.sum_prod_type]; dsimp only; apply sum_congr rfl; intro i _
      apply sum_congr rfl; intro j _
      rw [mul_pow, Real.sq_sqrt (hw i j)]
    rw [e1, e2, e3]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  -- Q ≤ 4DA
  have hT1 : ∑ i, ∑ j, wt i j * f i ^ 2 ≤ D * ∑ i, f i ^ 2 := by
    calc ∑ i, ∑ j, wt i j * f i ^ 2 = ∑ i, f i ^ 2 * ∑ j, wt i j := by
          apply sum_congr rfl; intro i _; rw [Finset.mul_sum]
          apply sum_congr rfl; intro j _; ring
      _ ≤ ∑ i, f i ^ 2 * D :=
          sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _))
      _ = D * ∑ i, f i ^ 2 := by rw [← Finset.sum_mul]; ring
  have hT2 : ∑ i, ∑ j, wt i j * f j ^ 2 ≤ D * ∑ i, f i ^ 2 := by
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, wt i j * f j ^ 2 = ∑ j, f j ^ 2 * ∑ i, wt i j := by
          apply sum_congr rfl; intro j _; rw [Finset.mul_sum]
          apply sum_congr rfl; intro i _; ring
      _ ≤ ∑ j, f j ^ 2 * D :=
          sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg _))
      _ = D * ∑ i, f i ^ 2 := by rw [← Finset.sum_mul]; ring
  have hQ1 : ∑ i, ∑ j, wt i j * (f i + f j) ^ 2 ≤
      2 * ∑ i, ∑ j, wt i j * f i ^ 2 + 2 * ∑ i, ∑ j, wt i j * f j ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply sum_le_sum; intro i _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply sum_le_sum; intro j _
    nlinarith [mul_nonneg (hw i j) (sq_nonneg (f i - f j))]
  have hQ : ∑ i, ∑ j, wt i j * (f i + f j) ^ 2 ≤ 4 * D * ∑ i, f i ^ 2 := by linarith
  -- combine
  set A := ∑ i, f i ^ 2 with hAdef
  set Dir := ∑ i, ∑ j, wt i j * (f i - f j) ^ 2 with hDirdef
  set P := ∑ i, ∑ j, wt i j * |f i ^ 2 - f j ^ 2| with hPdef
  set m := (Fintype.card Ω : ℝ) with hm
  have hm0 : 0 ≤ m := by positivity
  have hlow : κ * m * A ≤ P := by
    have : κ * m * A ≤ κ * (2 * Z.card * A) := by
      have := mul_le_mul_of_nonneg_right hZc hA
      nlinarith [mul_le_mul_of_nonneg_left this hκ]
    nlinarith [mul_le_mul_of_nonneg_left hpairs hκ]
  have hlow0 : 0 ≤ κ * m * A := by positivity
  have hsq : (κ * m * A) ^ 2 ≤ Dir * (4 * D * A) := by
    calc (κ * m * A) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ hlow0 hlow 2
      _ ≤ Dir * _ := hCS
      _ ≤ Dir * (4 * D * A) := mul_le_mul_of_nonneg_left hQ hDir
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · rw [← hA0]; simp [hDir]
  rcases le_or_gt D 0 with hD | hD
  · have : κ ^ 2 * m ^ 2 / (4 * D) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    nlinarith
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have key : (κ ^ 2 * m ^ 2 * A) * A ≤ (Dir * (4 * D)) * A := by nlinarith
    exact le_of_mul_le_mul_right key hApos

end T56aux

end BinaryThreeLCC.JM

open BinaryThreeLCC.JM BinaryThreeLCC.JM.T56aux

open Finset in
/-- T5: Poincaré inequality from cut density. -/
theorem solution {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (wt : Ω → Ω → ℝ) (hw : ∀ i j, 0 ≤ wt i j) (D : ℝ)
    (hrow : ∀ i, ∑ j, wt i j ≤ D) (hcol : ∀ j, ∑ i, wt i j ≤ D)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hcut : ∀ S : Finset Ω, κ * S.card * (Finset.univ \ S).card ≤
      ∑ i ∈ S, ∑ j ∈ Finset.univ \ S, wt i j)
    (h : Ω → ℝ) (hsum : ∑ i, h i = 0) :
    κ ^ 2 * (Fintype.card Ω : ℝ) ^ 2 / (4 * D) * ∑ i, h i ^ 2 ≤
      ∑ i, ∑ j, wt i j * (h i - h j) ^ 2 := by
  obtain ⟨c, hc1, hc2⟩ := T56aux.exists_median h
  set K := κ ^ 2 * (Fintype.card Ω : ℝ) ^ 2 / (4 * D) with hK
  set f : Ω → ℝ := fun i => max (h i - c) 0 with hf
  set g : Ω → ℝ := fun i => max (-(h i - c)) 0 with hg
  have hDirx : ∑ i, ∑ j, wt i j * (f i - f j) ^ 2 + ∑ i, ∑ j, wt i j * (g i - g j) ^ 2 ≤
      ∑ i, ∑ j, wt i j * (h i - h j) ^ 2 := by
    rw [← sum_add_distrib]; apply sum_le_sum; intro i _
    rw [← sum_add_distrib]; apply sum_le_sum; intro j _
    have := T56aux.pt_posneg (h i - c) (h j - c)
    have hxe : h i - h j = (h i - c) - (h j - c) := by ring
    rw [hxe, ← mul_add]; exact mul_le_mul_of_nonneg_left this (hw i j)
  have hcount1 := card_filter_add_card_filter_not (s := (univ : Finset Ω))
    (fun i => c < h i)
  have hcount2 := card_filter_add_card_filter_not (s := (univ : Finset Ω))
    (fun i => h i < c)
  rw [card_univ] at hcount1 hcount2
  have hfZ := T56aux.pos_part wt hw D hrow hcol κ hκ hcut f (fun i => le_max_right _ _)
    (univ.filter (fun i => ¬ c < h i))
    (by intro i hi; simp only [mem_filter, mem_univ, true_and, not_lt] at hi
        simp only [f]; exact max_eq_right (by linarith))
    (by have hn : Fintype.card Ω ≤ 2 * (univ.filter (fun i => ¬ c < h i)).card := by omega
        exact_mod_cast hn)
  have hgZ := T56aux.pos_part wt hw D hrow hcol κ hκ hcut g (fun i => le_max_right _ _)
    (univ.filter (fun i => ¬ h i < c))
    (by intro i hi; simp only [mem_filter, mem_univ, true_and, not_lt] at hi
        simp only [g]; exact max_eq_right (by linarith))
    (by have hn : Fintype.card Ω ≤ 2 * (univ.filter (fun i => ¬ h i < c)).card := by omega
        exact_mod_cast hn)
  have hsq : ∑ i, h i ^ 2 ≤ ∑ i, f i ^ 2 + ∑ i, g i ^ 2 := by
    have e : ∀ i, f i ^ 2 + g i ^ 2 = (h i - c) ^ 2 := by
      intro i; simp only [f, g]
      rcases le_total (h i - c) 0 with hh | hh
      · rw [max_eq_right hh, max_eq_left (neg_nonneg.mpr hh)]; ring
      · rw [max_eq_left hh, max_eq_right (neg_nonpos.mpr hh)]; ring
    rw [← sum_add_distrib, sum_congr rfl (fun i _ => e i)]
    have : ∑ i, (h i - c) ^ 2 = ∑ i, h i ^ 2 - 2 * c * ∑ i, h i +
        (Fintype.card Ω : ℝ) * c ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      rw [show (Fintype.card Ω : ℝ) * c ^ 2 = ∑ _i : Ω, c ^ 2 by simp]
      rw [← Finset.sum_add_distrib]; apply sum_congr rfl; intro i _; ring
    rw [this, hsum]
    have : 0 ≤ (Fintype.card Ω : ℝ) * c ^ 2 := by positivity
    linarith
  have hDirnn : 0 ≤ ∑ i, ∑ j, wt i j * (h i - h j) ^ 2 :=
    sum_nonneg (fun i _ => sum_nonneg (fun j _ => mul_nonneg (hw i j) (sq_nonneg _)))
  by_cases hK0 : 0 ≤ K
  · calc K * ∑ i, h i ^ 2 ≤ K * (∑ i, f i ^ 2 + ∑ i, g i ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hK0
      _ = K * ∑ i, f i ^ 2 + K * ∑ i, g i ^ 2 := by ring
      _ ≤ _ := add_le_add hfZ hgZ
      _ ≤ _ := hDirx
  · push_neg at hK0
    have : 0 ≤ ∑ i, h i ^ 2 := sum_nonneg (fun i _ => sq_nonneg _)
    nlinarith


namespace BinaryThreeLCC.JM

open Finset in
/-- T6: one-step variance contraction of the lazy averaged walk. -/
theorem variance_step {Ω Λ : Type} [Fintype Ω] [Fintype Λ] [DecidableEq Ω]
    (ρ : Λ → Ω → Ω)
    (hdbl : ∀ u, (Finset.univ.filter (fun p : Λ × Ω => ρ p.1 p.2 = u)).card = Fintype.card Λ)
    (γ : ℝ) (hpoinc : ∀ h : Ω → ℝ, ∑ i, h i = 0 →
      4 * Fintype.card Λ * γ * ∑ i, h i ^ 2 ≤ ∑ i, ∑ a, (h i - h (ρ a i)) ^ 2)
    (g : Ω → ℝ) :
    ∑ a, ∑ j, (g j + g (ρ a j) - (∑ j', (g j' + g (ρ a j'))) / Fintype.card Ω) ^ 2 ≤
      4 * Fintype.card Λ * (1 - γ) * ∑ j, (g j - (∑ j', g j') / Fintype.card Ω) ^ 2 := by
  by_cases hm : Fintype.card Ω = 0
  · have : IsEmpty Ω := Fintype.card_eq_zero_iff.mp hm
    simp
  have hmpos : (0:ℝ) < Fintype.card Ω := by exact_mod_cast Nat.pos_of_ne_zero hm
  set m : ℝ := (Fintype.card Ω : ℝ) with hmdef
  set N : ℝ := (Fintype.card Λ : ℝ) with hNdef
  set μ := (∑ j', g j') / m with hμ
  set hh : Ω → ℝ := fun j => g j - μ with hhdef
  have hsum0 : ∑ j, hh j = 0 := by
    simp only [hh, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, μ]
    field_simp; ring
  have transport : ∀ F : Ω → ℝ, ∑ a, ∑ j, F (ρ a j) = N * ∑ u, F u := by
    intro F
    rw [← Fintype.sum_prod_type' (f := fun a j => F (ρ a j))]
    rw [← Finset.sum_fiberwise (s := univ) (g := fun p : Λ × Ω => ρ p.1 p.2)
      (f := fun p => F (ρ p.1 p.2))]
    rw [mul_sum]; apply sum_congr rfl; intro u _
    rw [sum_congr rfl (g := fun _ => F u) (by intro p hp; rw [(mem_filter.mp hp).2])]
    rw [sum_const, hdbl u, nsmul_eq_mul]
  -- variance ≤ second moment
  have hvar : ∀ a, ∑ j, (g j + g (ρ a j) - (∑ j', (g j' + g (ρ a j'))) / m) ^ 2 ≤
      ∑ j, (hh j + hh (ρ a j)) ^ 2 := by
    intro a
    set z : Ω → ℝ := fun j => hh j + hh (ρ a j) with hz
    have hzz : ∀ j, g j + g (ρ a j) - (∑ j', (g j' + g (ρ a j'))) / m =
        z j - (∑ j', z j') / m := by
      intro j
      have : ∑ j', z j' = ∑ j', (g j' + g (ρ a j')) - 2 * m * μ := by
        simp only [z, hh, sum_add_distrib, sum_sub_distrib, sum_const, card_univ,
          nsmul_eq_mul]
        ring
      rw [this]; simp only [z, hh]; field_simp; ring
    simp_rw [hzz]
    have hid : ∑ j, (z j - (∑ j', z j') / m) ^ 2 =
        ∑ j, z j ^ 2 - (∑ j', z j') ^ 2 / m := by
      have e : ∀ j, (z j - (∑ j', z j') / m) ^ 2 =
          z j ^ 2 - 2 * ((∑ j', z j') / m) * z j + ((∑ j', z j') / m) ^ 2 := by
        intro j; ring
      simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
        nsmul_eq_mul]
      field_simp; ring
    rw [hid]
    have := div_nonneg (sq_nonneg (∑ j', z j')) hmpos.le
    linarith
  have hA : ∑ j, (g j - (∑ j', g j') / m) ^ 2 = ∑ j, hh j ^ 2 := rfl
  rw [hA]
  set A := ∑ j, hh j ^ 2 with hAdef
  set X := ∑ a, ∑ j, hh j * hh (ρ a j) with hXdef
  have hconst : ∑ _a : Λ, ∑ j, hh j ^ 2 = N * A := by
    simp [sum_const, card_univ, nsmul_eq_mul, N, A]
  have E1 : ∑ a, ∑ j, (hh j + hh (ρ a j)) ^ 2 = N * A + N * A + 2 * X := by
    have : ∑ a, ∑ j, (hh j + hh (ρ a j)) ^ 2 =
        ∑ _a : Λ, ∑ j, hh j ^ 2 + ∑ a, ∑ j, hh (ρ a j) ^ 2 + 2 * X := by
      simp only [X, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl; intro a _; apply sum_congr rfl; intro j _; ring
    rw [this, hconst, transport (fun u => hh u ^ 2)]
  have E2 : ∑ i, ∑ a, (hh i - hh (ρ a i)) ^ 2 = N * A + N * A - 2 * X := by
    rw [sum_comm]
    have : ∑ a, ∑ j, (hh j - hh (ρ a j)) ^ 2 =
        ∑ _a : Λ, ∑ j, hh j ^ 2 + ∑ a, ∑ j, hh (ρ a j) ^ 2 - 2 * X := by
      simp only [X, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      apply sum_congr rfl; intro a _; apply sum_congr rfl; intro j _; ring
    rw [this, hconst, transport (fun u => hh u ^ 2)]
  have hP := hpoinc hh hsum0
  rw [E2] at hP
  calc ∑ a, ∑ j, (g j + g (ρ a j) - (∑ j', (g j' + g (ρ a j'))) / m) ^ 2
      ≤ ∑ a, ∑ j, (hh j + hh (ρ a j)) ^ 2 := sum_le_sum (fun a _ => hvar a)
    _ = N * A + N * A + 2 * X := E1
    _ ≤ 4 * N * (1 - γ) * A := by linarith

end BinaryThreeLCC.JM
