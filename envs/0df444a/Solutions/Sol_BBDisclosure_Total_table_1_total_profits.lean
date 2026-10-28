-- Prove2me | solution 1 for BBDisclosure.Total.table_1_total_profits
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:18:10.839161+00:00
-- url     : https://prove2.me/submissions/15886e94-7fd7-414c-83e3-05b4f99b8b3e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BBDisclosure_Total_Stage2
import Definitions.Def_BBDisclosure_Total_Game
import Theorems.Thm_BBDisclosure_Total_equation_9
import Theorems.Thm_BBDisclosure_Total_equation_17
import Theorems.Thm_BBDisclosure_Total_equation_5
import Theorems.Thm_BBDisclosure_Total_equation_14

namespace BBDAuxC

/-- clamp helper: `min L (max 0 t)` equals `t` when `0 ≤ t ≤ L`. -/
lemma clamp_eq {L t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ L) : min L (max 0 t) = t := by
  rw [max_eq_right h0, min_eq_right h1]

/-- Uniqueness of the Nash equilibrium of a turf price game. The incumbent charges `a`, the
poacher `b`; the incumbent's demand is `min L (max 0 ((K + b - a) / 2))` on a segment of length
`L`. If `0 ≤ K < 4L`, the only equilibrium in nonnegative prices is the interior one. -/
lemma turf_unique (K L a b : ℝ) (hL : 0 < L) (hK0 : 0 ≤ K) (hK : K ≤ 4 * L) (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hA : ∀ a', 0 ≤ a' → a' * min L (max 0 ((K + b - a') / 2)) ≤
      a * min L (max 0 ((K + b - a) / 2)))
    (hB : ∀ b', 0 ≤ b' → b' * (L - min L (max 0 ((K + b' - a) / 2))) ≤
      b * (L - min L (max 0 ((K + b - a) / 2)))) :
    a = (K + 2 * L) / 3 ∧ b = (4 * L - K) / 3 := by
  set z := (K + b - a) / 2 with hz
  -- Case 1: z ≤ 0
  rcases le_or_gt z 0 with hz0 | hz0
  · exfalso
    have hD : min L (max 0 z) = 0 := by rw [max_eq_left hz0, min_eq_right hL.le]
    rcases lt_or_ge 0 (K + b) with hKb | hKb
    · have h := hA ((K + b) / 2) (by linarith)
      rw [hD, mul_zero] at h
      rcases le_total ((K + b - (K + b) / 2) / 2) L with h1 | h1
      · rw [clamp_eq (by linarith) h1] at h
        nlinarith
      · rw [max_eq_right (by linarith), min_eq_left h1] at h
        nlinarith
    · have hK0' : K = 0 := by linarith
      have hb0 : b = 0 := by linarith
      have h := hB L hL.le
      rw [hD, hb0, zero_mul] at h
      have : min L (max 0 ((K + L - a) / 2)) ≤ L / 2 := by
        apply min_le_of_right_le
        apply max_le (by linarith)
        rw [hK0']; linarith
      nlinarith
  -- Case 2: z ≥ L
  rcases le_or_gt L z with hzL | hzL
  · have hD : min L (max 0 z) = L := by rw [max_eq_right (by linarith), min_eq_left hzL]
    have hi : a = K + b - 2 * L := by
      have h := hA (K + b - 2 * L) (by linarith)
      rw [hD, show (K + b - (K + b - 2 * L)) / 2 = L by ring, max_eq_right hL.le, min_self] at h
      have : K + b - 2 * L ≤ a := le_of_mul_le_mul_right h hL
      linarith
    have hb0 : b = 0 := by
      by_contra hbne
      have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbne)
      have h := hB (b / 2) (by linarith)
      rw [hD, sub_self, mul_zero] at h
      have h5 : min L (max 0 ((K + b / 2 - a) / 2)) < L := by
        apply min_lt_of_right_lt; apply max_lt hL; rw [hi]; linarith
      have : 0 < b / 2 * (L - min L (max 0 ((K + b / 2 - a) / 2))) :=
        mul_pos (by linarith) (by linarith)
      linarith
    have h := hA (K / 2) (by linarith)
    rw [hD] at h
    have hge : min L (K / 4) ≤ min L (max 0 ((K + b - K / 2) / 2)) := by
      apply min_le_min (le_refl _)
      apply le_max_of_le_right
      linarith
    have h3 : K / 2 * min L (K / 4) ≤ a * L := by
      have := mul_le_mul_of_nonneg_left hge (show 0 ≤ K / 2 by linarith)
      linarith
    rcases le_total L (K / 4) with h4 | h4
    · have hK4 : K = 4 * L := by linarith
      constructor <;> linarith
    · rw [min_eq_right h4, hi, hb0] at h3
      have hK4 : K = 4 * L := by nlinarith [sq_nonneg (K - 4 * L)]
      constructor <;> linarith
  -- Case 3: interior
  have hD : min L (max 0 z) = z := clamp_eq hz0.le hzL.le
  rw [hD] at hA hB
  set m := min z (L - z) with hm
  have hm0 : 0 < m := lt_min hz0 (by linarith)
  have hmz : m ≤ z := min_le_left _ _
  have hmL : m ≤ L - z := min_le_right _ _
  -- incumbent first-order condition
  have hFA : K + b - 2 * a = 0 := by
    by_contra hg
    rcases lt_or_gt_of_ne hg with hneg | hpos
    · set d := -(min m (-(K + b - 2 * a))) / 4 with hd
      have e1 : min m (-(K + b - 2 * a)) ≤ m := min_le_left _ _
      have e2 : min m (-(K + b - 2 * a)) ≤ -(K + b - 2 * a) := min_le_right _ _
      have e3 : 0 < min m (-(K + b - 2 * a)) := lt_min hm0 (by linarith)
      have h := hA (a + d) (by rw [hd]; linarith)
      rw [clamp_eq (by rw [hd]; linarith) (by rw [hd]; linarith)] at h
      rw [hz] at h
      have : 0 < (-d) * (-(K + b - 2 * a) + d) := mul_pos (by rw [hd]; linarith) (by rw [hd]; linarith)
      nlinarith
    · set d := (min m (K + b - 2 * a)) / 4 with hd
      have e1 : min m (K + b - 2 * a) ≤ m := min_le_left _ _
      have e2 : min m (K + b - 2 * a) ≤ K + b - 2 * a := min_le_right _ _
      have e3 : 0 < min m (K + b - 2 * a) := lt_min hm0 hpos
      have h := hA (a + d) (by rw [hd]; linarith)
      rw [clamp_eq (by rw [hd]; linarith) (by rw [hd]; linarith)] at h
      rw [hz] at h
      have : 0 < d * ((K + b - 2 * a) - d) := mul_pos (by rw [hd]; linarith) (by rw [hd]; linarith)
      nlinarith
  -- poacher first-order condition
  have hFB : 2 * L - K + a - 2 * b = 0 := by
    by_contra hg
    rcases lt_or_gt_of_ne hg with hneg | hpos
    · set d := -(min m (-(2 * L - K + a - 2 * b))) / 4 with hd
      have e1 : min m (-(2 * L - K + a - 2 * b)) ≤ m := min_le_left _ _
      have e2 : min m (-(2 * L - K + a - 2 * b)) ≤ -(2 * L - K + a - 2 * b) := min_le_right _ _
      have e3 : 0 < min m (-(2 * L - K + a - 2 * b)) := lt_min hm0 (by linarith)
      have h := hB (b + d) (by rw [hd]; linarith)
      rw [clamp_eq (by rw [hd]; linarith) (by rw [hd]; linarith)] at h
      rw [hz] at h
      have : 0 < (-d) * (-(2 * L - K + a - 2 * b) + d) :=
        mul_pos (by rw [hd]; linarith) (by rw [hd]; linarith)
      nlinarith
    · set d := (min m (2 * L - K + a - 2 * b)) / 4 with hd
      have e1 : min m (2 * L - K + a - 2 * b) ≤ m := min_le_left _ _
      have e2 : min m (2 * L - K + a - 2 * b) ≤ 2 * L - K + a - 2 * b := min_le_right _ _
      have e3 : 0 < min m (2 * L - K + a - 2 * b) := lt_min hm0 hpos
      have h := hB (b + d) (by rw [hd]; linarith)
      rw [clamp_eq (by rw [hd]; linarith) (by rw [hd]; linarith)] at h
      rw [hz] at h
      have : 0 < d * ((2 * L - K + a - 2 * b) - d) :=
        mul_pos (by rw [hd]; linarith) (by rw [hd]; linarith)
      nlinarith
  constructor <;> linarith

open BBDisclosure.Stage2

lemma one_sub_clamp {x1 t : ℝ} (hx : x1 ≤ 1) :
    1 - min 1 (max x1 t) = min (1 - x1) (max 0 (1 - t)) := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- Equilibrium prices on A's turf. -/
lemma nashA_val (x1 u w : ℝ) (p : ℝ × ℝ) (hx : 0 < x1) (hK0 : 0 ≤ 1 + u - w)
    (hK : 1 + u - w ≤ 4 * x1) (h : IsTurfNashA x1 u w p) :
    p.1 = (1 + 2 * x1 + u - w) / 3 ∧ p.2 = (4 * x1 - 1 - u + w) / 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hx' : ∀ a b : ℝ, xaTurf x1 a b u w = min x1 (max 0 (((1 + u - w) + b - a) / 2)) := by
    intro a b; unfold xaTurf; rw [show (1 + b - a + u - w) / 2 = ((1 + u - w) + b - a) / 2 by ring]
  have := turf_unique (1 + u - w) x1 p.1 p.2 hx hK0 hK h1 h2
    (fun a' ha' => by have := h3 a' ha'; simpa [revAturfA, hx'] using this)
    (fun b' hb' => by have := h4 b' hb'; simpa [revBturfA, hx'] using this)
  constructor <;> linarith [this.1, this.2]

/-- Equilibrium prices on B's turf. -/
lemma nashB_val (x1 u w : ℝ) (p : ℝ × ℝ) (hx : x1 < 1) (hK0 : 0 ≤ 1 + w - u)
    (hK : 1 + w - u ≤ 4 * (1 - x1)) (h : IsTurfNashB x1 u w p) :
    p.1 = (3 - 4 * x1 + u - w) / 3 ∧ p.2 = (3 - 2 * x1 + w - u) / 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hx' : ∀ a b : ℝ, 1 - xbTurf x1 a b u w = min (1 - x1) (max 0 (((1 + w - u) + a - b) / 2)) := by
    intro a b; unfold xbTurf; rw [one_sub_clamp hx.le]
    rw [show 1 - (1 + b - a + u - w) / 2 = ((1 + w - u) + a - b) / 2 by ring]
  have hy : ∀ a b : ℝ, xbTurf x1 a b u w - x1 = (1 - x1) - (1 - xbTurf x1 a b u w) := by
    intro a b; ring
  have := turf_unique (1 + w - u) (1 - x1) p.2 p.1 (by linarith) hK0 hK h2 h1
    (fun a' ha' => by have := h4 a' ha'; simpa [revBturfB, hx'] using this)
    (fun b' hb' => by have := h3 b' hb'; simpa [revAturfB, hy, hx'] using this)
  constructor <;> linarith [this.1, this.2]

noncomputable def ind (qh q : ℝ) : ℝ := if qh < q then 1 else 0

lemma bel_nonneg {qh : ℝ} (h0 : 0 ≤ qh) (q : ℝ) : 0 ≤ bel qh q := by
  unfold bel; split_ifs with h <;> linarith

lemma bel_mono {qh : ℝ} (h0 : 0 ≤ qh) : Monotone (bel qh) := by
  intro x y hxy
  unfold bel
  split_ifs with h1 h2 h2 <;> linarith

lemma bel_sq_mono {qh : ℝ} (h0 : 0 ≤ qh) : Monotone (fun q => bel qh q ^ 2) := by
  intro x y hxy
  have := bel_mono h0 hxy
  have := bel_nonneg h0 x
  dsimp only
  nlinarith

lemma ind_mono (qh : ℝ) : Monotone (ind qh) := by
  intro x y hxy
  unfold ind
  split_ifs with h1 h2 h2 <;> linarith

lemma int_bel {qh : ℝ} (h0 : 0 ≤ qh) (h1 : qh ≤ 1) : ∫ q in (0 : ℝ)..1, bel qh q = 1 / 2 := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (bel qh) MeasureTheory.volume a b :=
    fun a b => (bel_mono h0).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 qh) (hi qh 1)]
  have e1 : ∫ q in (0 : ℝ)..qh, bel qh q = ∫ q in (0 : ℝ)..qh, qh / 2 :=
    intervalIntegral.integral_congr (fun q hq => by
      rw [Set.uIcc_of_le h0] at hq; simp [bel, not_lt.2 hq.2])
  have e2 : ∫ q in qh..1, bel qh q = ∫ q in qh..1, q :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun q hq => by
      rw [Set.uIoc_of_le h1] at hq; simp [bel, hq.1]))
  rw [e1, e2, intervalIntegral.integral_const, integral_id]
  simp; ring

lemma int_bel_sq {qh : ℝ} (h0 : 0 ≤ qh) (h1 : qh ≤ 1) :
    ∫ q in (0 : ℝ)..1, bel qh q ^ 2 = 1 / 3 - qh ^ 3 / 12 := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun q => bel qh q ^ 2) MeasureTheory.volume a b :=
    fun a b => (bel_sq_mono h0).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 qh) (hi qh 1)]
  have e1 : ∫ q in (0 : ℝ)..qh, bel qh q ^ 2 = ∫ q in (0 : ℝ)..qh, (qh / 2) ^ 2 :=
    intervalIntegral.integral_congr (fun q hq => by
      rw [Set.uIcc_of_le h0] at hq; simp [bel, not_lt.2 hq.2])
  have e2 : ∫ q in qh..1, bel qh q ^ 2 = ∫ q in qh..1, q ^ 2 :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun q hq => by
      rw [Set.uIoc_of_le h1] at hq; simp [bel, hq.1]))
  rw [e1, e2, intervalIntegral.integral_const, integral_pow]
  simp; ring

lemma int_ind {qh : ℝ} (h0 : 0 ≤ qh) (h1 : qh ≤ 1) : ∫ q in (0 : ℝ)..1, ind qh q = 1 - qh := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (ind qh) MeasureTheory.volume a b :=
    fun a b => (ind_mono qh).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 qh) (hi qh 1)]
  have e1 : ∫ q in (0 : ℝ)..qh, ind qh q = ∫ q in (0 : ℝ)..qh, (0 : ℝ) :=
    intervalIntegral.integral_congr (fun q hq => by
      rw [Set.uIcc_of_le h0] at hq; simp [ind, not_lt.2 hq.2])
  have e2 : ∫ q in qh..1, ind qh q = ∫ q in qh..1, (1 : ℝ) :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun q hq => by
      rw [Set.uIoc_of_le h1] at hq; simp [ind, hq.1]))
  rw [e1, e2, intervalIntegral.integral_const, intervalIntegral.integral_const]
  simp

lemma int1 {h h' : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hh'0 : 0 ≤ h') (hh'1 : h' ≤ 1)
    (A B C B' C' E E' : ℝ) :
    ∫ q in (0 : ℝ)..1, (A + B * bel h q + C * bel h q ^ 2 + B' * bel h' q + C' * bel h' q ^ 2
      + E * ind h q + E' * ind h' q) =
      A + B / 2 + C * (1 / 3 - h ^ 3 / 12) + B' / 2 + C' * (1 / 3 - h' ^ 3 / 12)
        + E * (1 - h) + E' * (1 - h') := by
  have i1 : IntervalIntegrable (fun q => bel h q) MeasureTheory.volume 0 1 :=
    (bel_mono hh0).intervalIntegrable
  have i2 : IntervalIntegrable (fun q => bel h q ^ 2) MeasureTheory.volume 0 1 :=
    (bel_sq_mono hh0).intervalIntegrable
  have i3 : IntervalIntegrable (fun q => bel h' q) MeasureTheory.volume 0 1 :=
    (bel_mono hh'0).intervalIntegrable
  have i4 : IntervalIntegrable (fun q => bel h' q ^ 2) MeasureTheory.volume 0 1 :=
    (bel_sq_mono hh'0).intervalIntegrable
  have i5 : IntervalIntegrable (fun q => ind h q) MeasureTheory.volume 0 1 :=
    (ind_mono h).intervalIntegrable
  have i6 : IntervalIntegrable (fun q => ind h' q) MeasureTheory.volume 0 1 :=
    (ind_mono h').intervalIntegrable
  have c0 : IntervalIntegrable (fun _ : ℝ => A) MeasureTheory.volume 0 1 := intervalIntegrable_const
  rw [intervalIntegral.integral_add (((((c0.add (i1.const_mul B)).add (i2.const_mul C)).add
      (i3.const_mul B')).add (i4.const_mul C')).add (i5.const_mul E)) (i6.const_mul E'),
    intervalIntegral.integral_add ((((c0.add (i1.const_mul B)).add (i2.const_mul C)).add
      (i3.const_mul B')).add (i4.const_mul C')) (i5.const_mul E),
    intervalIntegral.integral_add (((c0.add (i1.const_mul B)).add (i2.const_mul C)).add
      (i3.const_mul B')) (i4.const_mul C'),
    intervalIntegral.integral_add ((c0.add (i1.const_mul B)).add (i2.const_mul C))
      (i3.const_mul B'),
    intervalIntegral.integral_add (c0.add (i1.const_mul B)) (i2.const_mul C),
    intervalIntegral.integral_add c0 (i1.const_mul B)]
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  rw [int_bel hh0 hh1, int_bel_sq hh0 hh1, int_bel hh'0 hh'1, int_bel_sq hh'0 hh'1,
    int_ind hh0 hh1, int_ind hh'0 hh'1]
  simp; ring

lemma dbl2 {ha ha' hb hb' : ℝ} (ha0 : 0 ≤ ha) (ha1 : ha ≤ 1) (ha'0 : 0 ≤ ha') (ha'1 : ha' ≤ 1)
    (hb0 : 0 ≤ hb) (hb1 : hb ≤ 1) (hb'0 : 0 ≤ hb') (hb'1 : hb' ≤ 1) (f : ℝ → ℝ → ℝ)
    (α β γ δ ε ζ β' γ' δ' ε' ζ' η η' : ℝ)
    (hf : ∀ x ∈ Set.uIcc (0 : ℝ) 1, ∀ y ∈ Set.uIcc (0 : ℝ) 1, f x y =
      α + β * bel ha x + γ * bel hb y + δ * bel ha x ^ 2 + ε * bel ha x * bel hb y
        + ζ * bel hb y ^ 2 + β' * bel ha' x + γ' * bel hb' y + δ' * bel ha' x ^ 2
        + ε' * bel ha' x * bel hb' y + ζ' * bel hb' y ^ 2 + η * ind ha x + η' * ind ha' x) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f x y =
      α + β / 2 + γ / 2 + δ * (1 / 3 - ha ^ 3 / 12) + ε / 4 + ζ * (1 / 3 - hb ^ 3 / 12)
        + β' / 2 + γ' / 2 + δ' * (1 / 3 - ha' ^ 3 / 12) + ε' / 4 + ζ' * (1 / 3 - hb' ^ 3 / 12)
        + η * (1 - ha) + η' * (1 - ha') := by
  have inner : ∀ x ∈ Set.uIcc (0 : ℝ) 1, ∫ y in (0 : ℝ)..1, f x y =
      (α + β * bel ha x + δ * bel ha x ^ 2 + β' * bel ha' x + δ' * bel ha' x ^ 2
        + η * ind ha x + η' * ind ha' x)
      + (γ + ε * bel ha x) / 2 + ζ * (1 / 3 - hb ^ 3 / 12)
      + (γ' + ε' * bel ha' x) / 2 + ζ' * (1 / 3 - hb' ^ 3 / 12) := by
    intro x hx
    rw [intervalIntegral.integral_congr (g := fun y =>
      (α + β * bel ha x + δ * bel ha x ^ 2 + β' * bel ha' x + δ' * bel ha' x ^ 2
        + η * ind ha x + η' * ind ha' x)
      + (γ + ε * bel ha x) * bel hb y + ζ * bel hb y ^ 2 + (γ' + ε' * bel ha' x) * bel hb' y
      + ζ' * bel hb' y ^ 2 + 0 * ind hb y + 0 * ind hb' y)
      (fun y hy => by simp only; rw [hf x hx y hy]; ring)]
    rw [int1 hb0 hb1 hb'0 hb'1]
    ring
  rw [intervalIntegral.integral_congr (g := fun x =>
      (α + γ / 2 + ζ * (1 / 3 - hb ^ 3 / 12) + γ' / 2 + ζ' * (1 / 3 - hb' ^ 3 / 12))
      + (β + ε / 2) * bel ha x + δ * bel ha x ^ 2 + (β' + ε' / 2) * bel ha' x
      + δ' * bel ha' x ^ 2 + η * ind ha x + η' * ind ha' x)
      (fun x hx => by simp only; rw [inner x hx]; ring)]
  rw [int1 ha0 ha1 ha'0 ha'1]
  ring

lemma bel_bounds {qh q : ℝ} (h0 : 0 ≤ qh) (h1 : qh ≤ 1) (hq : q ∈ Set.uIcc (0 : ℝ) 1) :
    qh / 2 ≤ bel qh q ∧ bel qh q ≤ 1 := by
  rw [Set.uIcc_of_le zero_le_one] at hq
  unfold bel
  split_ifs with h <;> constructor <;> linarith [hq.1, hq.2]

lemma revA_val (x1 u w : ℝ) (hK0 : 0 ≤ 1 + u - w) (hK : 1 + u - w ≤ 4 * x1) :
    revAturfA x1 u w ((1 + 2 * x1 + u - w) / 3, (4 * x1 - 1 - u + w) / 3) =
      (1 + 2 * x1 + u - w) ^ 2 / 18 := by
  unfold revAturfA xaTurf
  simp only
  rw [show (1 + (4 * x1 - 1 - u + w) / 3 - (1 + 2 * x1 + u - w) / 3 + u - w) / 2
      = (1 + 2 * x1 + u - w) / 6 by ring, clamp_eq (by linarith) (by linarith)]
  ring

lemma revB_val (x1 u w : ℝ) (hK0 : 0 ≤ 1 + w - u) (hK : 1 + w - u ≤ 4 * (1 - x1)) :
    revAturfB x1 u w ((3 - 4 * x1 + u - w) / 3, (3 - 2 * x1 + w - u) / 3) =
      (3 - 4 * x1 + u - w) ^ 2 / 18 := by
  unfold revAturfB xbTurf
  simp only
  rw [show (1 + (3 - 2 * x1 + w - u) / 3 - (3 - 4 * x1 + u - w) / 3 + u - w) / 2
      = (3 + 2 * x1 + u - w) / 6 by ring, max_eq_right (by linarith), min_eq_right (by linarith)]
  ring

lemma ite_ind (h q k : ℝ) : (if h < q then k else 0) = k * ind h q := by
  unfold ind; split_ifs <;> ring

lemma revBA_val (x1 u w : ℝ) (hK0 : 0 ≤ 1 + u - w) (hK : 1 + u - w ≤ 4 * x1) :
    revBturfA x1 u w ((1 + 2 * x1 + u - w) / 3, (4 * x1 - 1 - u + w) / 3) =
      (4 * x1 - 1 - u + w) ^ 2 / 18 := by
  unfold revBturfA xaTurf
  simp only
  rw [show (1 + (4 * x1 - 1 - u + w) / 3 - (1 + 2 * x1 + u - w) / 3 + u - w) / 2
      = (1 + 2 * x1 + u - w) / 6 by ring, clamp_eq (by linarith) (by linarith)]
  ring

lemma revBB_val (x1 u w : ℝ) (hK0 : 0 ≤ 1 + w - u) (hK : 1 + w - u ≤ 4 * (1 - x1)) :
    revBturfB x1 u w ((3 - 4 * x1 + u - w) / 3, (3 - 2 * x1 + w - u) / 3) =
      (3 - 2 * x1 + w - u) ^ 2 / 18 := by
  unfold revBturfB xbTurf
  simp only
  rw [show (1 + (3 - 2 * x1 + w - u) / 3 - (3 - 4 * x1 + u - w) / 3 + u - w) / 2
      = (3 + 2 * x1 + u - w) / 6 by ring, max_eq_right (by linarith), min_eq_right (by linarith)]
  ring

lemma sgl {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (f : ℝ → ℝ) (A B C : ℝ)
    (hf : ∀ y ∈ Set.uIcc (0 : ℝ) 1, f y = A + B * bel h y + C * bel h y ^ 2) :
    ∫ y in (0 : ℝ)..1, f y = A + B / 2 + C * (1 / 3 - h ^ 3 / 12) := by
  rw [intervalIntegral.integral_congr (g := fun y => A + B * bel h y + C * bel h y ^ 2
      + 0 * bel h y + 0 * bel h y ^ 2 + 0 * ind h y + 0 * ind h y)
      (fun y hy => by simp only; rw [hf y hy]; ring)]
  rw [int1 h0 h1 h0 h1]
  ring

lemma dbl3 {ha ha' hb hb' : ℝ} (ha0 : 0 ≤ ha) (ha1 : ha ≤ 1) (ha'0 : 0 ≤ ha') (ha'1 : ha' ≤ 1)
    (hb0 : 0 ≤ hb) (hb1 : hb ≤ 1) (hb'0 : 0 ≤ hb') (hb'1 : hb' ≤ 1) (f : ℝ → ℝ → ℝ)
    (α β γ δ ε ζ β' γ' δ' ε' ζ' θ θ' : ℝ)
    (hf : ∀ x ∈ Set.uIcc (0 : ℝ) 1, ∀ y ∈ Set.uIcc (0 : ℝ) 1, f x y =
      α + β * bel ha x + γ * bel hb y + δ * bel ha x ^ 2 + ε * bel ha x * bel hb y
        + ζ * bel hb y ^ 2 + β' * bel ha' x + γ' * bel hb' y + δ' * bel ha' x ^ 2
        + ε' * bel ha' x * bel hb' y + ζ' * bel hb' y ^ 2 + θ * ind hb y + θ' * ind hb' y) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f x y =
      α + β / 2 + γ / 2 + δ * (1 / 3 - ha ^ 3 / 12) + ε / 4 + ζ * (1 / 3 - hb ^ 3 / 12)
        + β' / 2 + γ' / 2 + δ' * (1 / 3 - ha' ^ 3 / 12) + ε' / 4 + ζ' * (1 / 3 - hb' ^ 3 / 12)
        + θ * (1 - hb) + θ' * (1 - hb') := by
  have inner : ∀ x ∈ Set.uIcc (0 : ℝ) 1, ∫ y in (0 : ℝ)..1, f x y =
      (α + β * bel ha x + δ * bel ha x ^ 2 + β' * bel ha' x + δ' * bel ha' x ^ 2)
      + (γ + ε * bel ha x) / 2 + ζ * (1 / 3 - hb ^ 3 / 12)
      + (γ' + ε' * bel ha' x) / 2 + ζ' * (1 / 3 - hb' ^ 3 / 12)
      + θ * (1 - hb) + θ' * (1 - hb') := by
    intro x hx
    rw [intervalIntegral.integral_congr (g := fun y =>
      (α + β * bel ha x + δ * bel ha x ^ 2 + β' * bel ha' x + δ' * bel ha' x ^ 2)
      + (γ + ε * bel ha x) * bel hb y + ζ * bel hb y ^ 2 + (γ' + ε' * bel ha' x) * bel hb' y
      + ζ' * bel hb' y ^ 2 + θ * ind hb y + θ' * ind hb' y)
      (fun y hy => by simp only; rw [hf x hx y hy]; ring)]
    rw [int1 hb0 hb1 hb'0 hb'1]
  rw [intervalIntegral.integral_congr (g := fun x =>
      (α + γ / 2 + ζ * (1 / 3 - hb ^ 3 / 12) + γ' / 2 + ζ' * (1 / 3 - hb' ^ 3 / 12)
        + θ * (1 - hb) + θ' * (1 - hb'))
      + (β + ε / 2) * bel ha x + δ * bel ha x ^ 2 + (β' + ε' / 2) * bel ha' x
      + δ' * bel ha' x ^ 2 + 0 * ind ha x + 0 * ind ha' x)
      (fun x hx => by simp only; rw [inner x hx]; ring)]
  rw [int1 ha0 ha1 ha'0 ha'1]
  ring

/-- A best-response threshold for a gain `A q² + B q` against a fixed nondisclosure level `P0`
is the root of `A h² + B h = P0`. -/
lemma thr_eq {A B P0 h : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (hbr : ∀ q ∈ Set.Icc (0 : ℝ) 1, (h < q → P0 ≤ A * q ^ 2 + B * q) ∧
      (q < h → A * q ^ 2 + B * q ≤ P0))
    (hlo : h = 0 → 0 < P0) (hhi : h = 1 → P0 < A + B) :
    A * h ^ 2 + B * h = P0 := by
  have hM : 0 < 2 * A + B + 1 := by linarith
  -- lower side
  have key1 : h < 1 → P0 ≤ A * h ^ 2 + B * h := by
    intro hh
    by_contra hcon
    push_neg at hcon
    set δ := P0 - (A * h ^ 2 + B * h) with hδ
    have hδ0 : 0 < δ := by linarith
    set t := min (1 - h) (δ / (2 * (2 * A + B + 1))) with ht
    have ht0 : 0 < t := lt_min (by linarith) (by positivity)
    have ht1 : t ≤ 1 - h := min_le_left _ _
    have ht2 : t ≤ δ / (2 * (2 * A + B + 1)) := min_le_right _ _
    have h3 := (hbr (h + t) ⟨by linarith, by linarith⟩).1 (by linarith)
    have h4 : t * (2 * (2 * A + B + 1)) ≤ δ := by
      rwa [le_div_iff₀ (by positivity)] at ht2
    have : A * (h + t) ^ 2 + B * (h + t) - (A * h ^ 2 + B * h) ≤ t * (2 * A + B) := by
      have : A * (h + t) ^ 2 + B * (h + t) - (A * h ^ 2 + B * h) = t * (A * (2 * h + t) + B) := by
        ring
      rw [this]
      have : A * (2 * h + t) ≤ 2 * A := by nlinarith
      nlinarith
    nlinarith
  have key2 : 0 < h → A * h ^ 2 + B * h ≤ P0 := by
    intro hh
    by_contra hcon
    push_neg at hcon
    set δ := (A * h ^ 2 + B * h) - P0 with hδ
    have hδ0 : 0 < δ := by linarith
    set t := min h (δ / (2 * (2 * A + B + 1))) with ht
    have ht0 : 0 < t := lt_min hh (by positivity)
    have ht1 : t ≤ h := min_le_left _ _
    have ht2 : t ≤ δ / (2 * (2 * A + B + 1)) := min_le_right _ _
    have h3 := (hbr (h - t) ⟨by linarith, by linarith⟩).2 (by linarith)
    have h4 : t * (2 * (2 * A + B + 1)) ≤ δ := by
      rwa [le_div_iff₀ (by positivity)] at ht2
    have : (A * h ^ 2 + B * h) - (A * (h - t) ^ 2 + B * (h - t)) ≤ t * (2 * A + B) := by
      have : (A * h ^ 2 + B * h) - (A * (h - t) ^ 2 + B * (h - t)) = t * (A * (2 * h - t) + B) := by
        ring
      rw [this]
      have : A * (2 * h - t) ≤ 2 * A := by nlinarith
      nlinarith
    nlinarith
  rcases eq_or_lt_of_le h0 with hz | hpos
  · -- h = 0 is impossible
    exfalso
    have hP := hlo hz.symm
    set t := min 1 (P0 / (2 * (A + B + 1))) with ht
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t ≤ P0 / (2 * (A + B + 1)) := min_le_right _ _
    have h3 := (hbr t ⟨ht0.le, ht1⟩).1 (by rw [← hz]; exact ht0)
    have h4 : t * (2 * (A + B + 1)) ≤ P0 := by
      rwa [le_div_iff₀ (by positivity)] at ht2
    have : A * t ^ 2 ≤ A * t := by nlinarith
    nlinarith
  rcases eq_or_lt_of_le h1 with ho | hlt
  · exfalso
    have := key2 hpos
    have := hhi ho
    rw [ho] at *
    nlinarith
  exact le_antisymm (key2 hpos) (key1 hlt)

end BBDAuxC

namespace BBDAuxC
open BBDisclosure.Stage2

lemma root_of_quad {c h : ℝ} (hc : 0 < c) (h0 : 0 ≤ h) (hq : 3 * h ^ 2 / 4 + h = 9 * c) :
    h = (2 * Real.sqrt (1 + 27 * c) - 2) / 3 := by
  have : Real.sqrt (1 + 27 * c) = (3 * h + 2) / 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by linarith) (by linarith)]
    nlinarith
  rw [this]; ring

lemma thrU_half (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) (e : ProfileU)
    (he : IsStage2EqU c (1 / 2) e) :
    e.qa = (2 * Real.sqrt (1 + 27 * c) - 2) / 3 ∧ e.qb = (2 * Real.sqrt (1 + 27 * c) - 2) / 3 := by
  obtain ⟨⟨hqa0, hqa1⟩, ⟨hqb0, hqb1⟩, hNA, hNB, hBRa, hBRb⟩ := he
  have VA : ∀ u ∈ Set.Icc (0 : ℝ) 1, (∫ qb in (0 : ℝ)..1,
      (revAturfA (1 / 2) u (bel e.qb qb) (e.σA u (bel e.qb qb)) +
        revAturfB (1 / 2) u (bel e.qb qb) (e.σB u (bel e.qb qb))))
      = (u ^ 2 + 2 * u + 1) / 9 + 1 / 9 * (1 / 3 - e.qb ^ 3 / 12) := by
    intro u ⟨hu0, hu1⟩
    refine (sgl hqb0 hqb1 _ (((2 + u) ^ 2 + (1 + u) ^ 2) / 18) (-(3 + 2 * u) / 9) (1 / 9)
      (fun y hy => ?_)).trans ?_
    · obtain ⟨w1, w2⟩ := bel_bounds hqb0 hqb1 hy
      have hA := nashA_val (1 / 2) _ _ _ (by norm_num) (by linarith) (by linarith)
        (hNA _ ⟨hu0, hu1⟩ _ ⟨by linarith, w2⟩)
      have hB := nashB_val (1 / 2) _ _ _ (by norm_num) (by linarith) (by linarith)
        (hNB _ ⟨hu0, hu1⟩ _ ⟨by linarith, w2⟩)
      have hA' : e.σA u (bel e.qb y) = ((1 + 2 * (1 / 2) + u - bel e.qb y) / 3,
          (4 * (1 / 2) - 1 - u + bel e.qb y) / 3) := Prod.ext hA.1 hA.2
      have hB' : e.σB u (bel e.qb y) = ((3 - 4 * (1 / 2) + u - bel e.qb y) / 3,
          (3 - 2 * (1 / 2) + bel e.qb y - u) / 3) := Prod.ext hB.1 hB.2
      rw [hA', hB', revA_val _ _ _ (by linarith) (by linarith),
        revB_val _ _ _ (by linarith) (by linarith)]
      ring
    · ring
  have VB : ∀ w ∈ Set.Icc (0 : ℝ) 1, (∫ qa in (0 : ℝ)..1,
      (revBturfA (1 / 2) (bel e.qa qa) w (e.σA (bel e.qa qa) w) +
        revBturfB (1 / 2) (bel e.qa qa) w (e.σB (bel e.qa qa) w)))
      = (w ^ 2 + 2 * w + 1) / 9 + 1 / 9 * (1 / 3 - e.qa ^ 3 / 12) := by
    intro w ⟨hw0, hw1⟩
    refine (sgl hqa0 hqa1 _ (((1 + w) ^ 2 + (2 + w) ^ 2) / 18) (-(3 + 2 * w) / 9) (1 / 9)
      (fun y hy => ?_)).trans ?_
    · obtain ⟨u1, u2⟩ := bel_bounds hqa0 hqa1 hy
      have hA := nashA_val (1 / 2) _ _ _ (by norm_num) (by linarith) (by linarith)
        (hNA _ ⟨by linarith, u2⟩ _ ⟨hw0, hw1⟩)
      have hB := nashB_val (1 / 2) _ _ _ (by norm_num) (by linarith) (by linarith)
        (hNB _ ⟨by linarith, u2⟩ _ ⟨hw0, hw1⟩)
      have hA' : e.σA (bel e.qa y) w = ((1 + 2 * (1 / 2) + bel e.qa y - w) / 3,
          (4 * (1 / 2) - 1 - bel e.qa y + w) / 3) := Prod.ext hA.1 hA.2
      have hB' : e.σB (bel e.qa y) w = ((3 - 4 * (1 / 2) + bel e.qa y - w) / 3,
          (3 - 2 * (1 / 2) + w - bel e.qa y) / 3) := Prod.ext hB.1 hB.2
      rw [hA', hB', revBA_val _ _ _ (by linarith) (by linarith),
        revBB_val _ _ _ (by linarith) (by linarith)]
      ring
    · ring
  have ea : 1 * e.qa ^ 2 + 2 * e.qa = 9 * c + e.qa ^ 2 / 4 + e.qa := by
    apply thr_eq (by norm_num) (by norm_num) hqa0 hqa1
    · intro q hq
      have hb := hBRa q hq
      simp only at hb
      rw [VA q hq, VA (e.qa / 2) ⟨by linarith, by linarith⟩] at hb
      constructor
      · intro h; have := hb.1 h; nlinarith
      · intro h; have := hb.2 h; nlinarith
    · intro _; positivity
    · intro h; rw [h]; linarith
  have eb : 1 * e.qb ^ 2 + 2 * e.qb = 9 * c + e.qb ^ 2 / 4 + e.qb := by
    apply thr_eq (by norm_num) (by norm_num) hqb0 hqb1
    · intro q hq
      have hb := hBRb q hq
      simp only at hb
      rw [VB q hq, VB (e.qb / 2) ⟨by linarith, by linarith⟩] at hb
      constructor
      · intro h; have := hb.1 h; nlinarith
      · intro h; have := hb.2 h; nlinarith
    · intro _; positivity
    · intro h; rw [h]; linarith
  exact ⟨root_of_quad hc0 hqa0 (by linarith), root_of_quad hc0 hqb0 (by linarith)⟩

lemma thrB_half (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) (e : ProfileBBD)
    (he : IsStage2EqBBD c (1 / 2) e) :
    e.qao = Real.sqrt (1 + 12 * c) - 1 ∧ e.qan = (Real.sqrt (1 + 108 * c) - 1) / 3 ∧
    e.qbo = Real.sqrt (1 + 12 * c) - 1 ∧ e.qbn = (Real.sqrt (1 + 108 * c) - 1) / 3 := by
  obtain ⟨⟨hao0, hao1⟩, ⟨han0, han1⟩, ⟨hbo0, hbo1⟩, ⟨hbn0, hbn1⟩, hNA, hNB,
    hBRao, hBRan, hBRbo, hBRbn⟩ := he
  have Vao : ∀ u ∈ Set.Icc (0 : ℝ) 1, (∫ qb in (0 : ℝ)..1,
      revAturfA (1 / 2) u (bel e.qbn qb) (e.σA u (bel e.qbn qb)))
      = (u ^ 2 + 3 * u + 2) / 18 + 1 / 18 * (1 / 3 - e.qbn ^ 3 / 12) := by
    intro u ⟨hu0, hu1⟩
    refine (sgl hbn0 hbn1 _ ((2 + u) ^ 2 / 18) (-(2 + u) / 9) (1 / 18) (fun y hy => ?_)).trans ?_
    · obtain ⟨w1, w2⟩ := bel_bounds hbn0 hbn1 hy
      have hA := nashA_val (1 / 2) _ _ _ (by norm_num) (by linarith) (by linarith)
        (hNA _ ⟨hu0, hu1⟩ _ ⟨by linarith, w2⟩)
      have hA' : e.σA u (bel e.qbn y) = ((1 + 2 * (1 / 2) + u - bel e.qbn y) / 3,
          (4 * (1 / 2) - 1 - u + bel e.qbn y) / 3) := Prod.ext hA.1 hA.2
      rw [hA', revA_val _ _ _ (by linarith) (by linarith)]
      ring
    · ring
  have Van : ∀ u ∈ Set.Icc (0 : ℝ) 1, (∫ qb in (0 : ℝ)..1,
      revAturfB (1 / 2) u (bel e.qbo qb) (e.σB u (bel e.qbo qb)))
      = (u ^ 2 + u) / 18 + 1 / 18 * (1 / 3 - e.qbo ^ 3 / 12) := by
    intro u ⟨hu0, hu1⟩
    refine (sgl hbo0 hbo1 _ ((1 + u) ^ 2 / 18) (-(1 + u) / 9) (1 / 18) (fun y hy => ?_)).trans ?_
    · obtain ⟨w1, w2⟩ := bel_bounds hbo0 hbo1 hy
      have hB := nashB_val (1 / 2) _ _ _ (by norm_num) (by linarith) (by linarith)
        (hNB _ ⟨hu0, hu1⟩ _ ⟨by linarith, w2⟩)
      have hB' : e.σB u (bel e.qbo y) = ((3 - 4 * (1 / 2) + u - bel e.qbo y) / 3,
          (3 - 2 * (1 / 2) + bel e.qbo y - u) / 3) := Prod.ext hB.1 hB.2
      rw [hB', revB_val _ _ _ (by linarith) (by linarith)]
      ring
    · ring
  have Vbo : ∀ w ∈ Set.Icc (0 : ℝ) 1, (∫ qa in (0 : ℝ)..1,
      revBturfB (1 / 2) (bel e.qan qa) w (e.σB (bel e.qan qa) w))
      = (w ^ 2 + 3 * w + 2) / 18 + 1 / 18 * (1 / 3 - e.qan ^ 3 / 12) := by
    intro w ⟨hw0, hw1⟩
    refine (sgl han0 han1 _ ((2 + w) ^ 2 / 18) (-(2 + w) / 9) (1 / 18) (fun y hy => ?_)).trans ?_
    · obtain ⟨u1, u2⟩ := bel_bounds han0 han1 hy
      have hB := nashB_val (1 / 2) _ _ _ (by norm_num) (by linarith) (by linarith)
        (hNB _ ⟨by linarith, u2⟩ _ ⟨hw0, hw1⟩)
      have hB' : e.σB (bel e.qan y) w = ((3 - 4 * (1 / 2) + bel e.qan y - w) / 3,
          (3 - 2 * (1 / 2) + w - bel e.qan y) / 3) := Prod.ext hB.1 hB.2
      rw [hB', revBB_val _ _ _ (by linarith) (by linarith)]
      ring
    · ring
  have Vbn : ∀ w ∈ Set.Icc (0 : ℝ) 1, (∫ qa in (0 : ℝ)..1,
      revBturfA (1 / 2) (bel e.qao qa) w (e.σA (bel e.qao qa) w))
      = (w ^ 2 + w) / 18 + 1 / 18 * (1 / 3 - e.qao ^ 3 / 12) := by
    intro w ⟨hw0, hw1⟩
    refine (sgl hao0 hao1 _ ((1 + w) ^ 2 / 18) (-(1 + w) / 9) (1 / 18) (fun y hy => ?_)).trans ?_
    · obtain ⟨u1, u2⟩ := bel_bounds hao0 hao1 hy
      have hA := nashA_val (1 / 2) _ _ _ (by norm_num) (by linarith) (by linarith)
        (hNA _ ⟨by linarith, u2⟩ _ ⟨hw0, hw1⟩)
      have hA' : e.σA (bel e.qao y) w = ((1 + 2 * (1 / 2) + bel e.qao y - w) / 3,
          (4 * (1 / 2) - 1 - bel e.qao y + w) / 3) := Prod.ext hA.1 hA.2
      rw [hA', revBA_val _ _ _ (by linarith) (by linarith)]
      ring
    · ring
  have eao : 1 * e.qao ^ 2 + 3 * e.qao = 9 * c + e.qao ^ 2 / 4 + 3 * e.qao / 2 := by
    apply thr_eq (by norm_num) (by norm_num) hao0 hao1
    · intro q hq
      have hb := hBRao q hq
      simp only at hb
      rw [Vao q hq, Vao (e.qao / 2) ⟨by linarith, by linarith⟩] at hb
      constructor
      · intro h; have := hb.1 h; nlinarith
      · intro h; have := hb.2 h; nlinarith
    · intro _; positivity
    · intro h; rw [h]; linarith
  have ean : 1 * e.qan ^ 2 + 1 * e.qan = 9 * c + e.qan ^ 2 / 4 + e.qan / 2 := by
    apply thr_eq (by norm_num) (by norm_num) han0 han1
    · intro q hq
      have hb := hBRan q hq
      simp only at hb
      rw [Van q hq, Van (e.qan / 2) ⟨by linarith, by linarith⟩] at hb
      constructor
      · intro h; have := hb.1 h; nlinarith
      · intro h; have := hb.2 h; nlinarith
    · intro _; positivity
    · intro h; rw [h]; linarith
  have ebo : 1 * e.qbo ^ 2 + 3 * e.qbo = 9 * c + e.qbo ^ 2 / 4 + 3 * e.qbo / 2 := by
    apply thr_eq (by norm_num) (by norm_num) hbo0 hbo1
    · intro q hq
      have hb := hBRbo q hq
      simp only at hb
      rw [Vbo q hq, Vbo (e.qbo / 2) ⟨by linarith, by linarith⟩] at hb
      constructor
      · intro h; have := hb.1 h; nlinarith
      · intro h; have := hb.2 h; nlinarith
    · intro _; positivity
    · intro h; rw [h]; linarith
  have ebn : 1 * e.qbn ^ 2 + 1 * e.qbn = 9 * c + e.qbn ^ 2 / 4 + e.qbn / 2 := by
    apply thr_eq (by norm_num) (by norm_num) hbn0 hbn1
    · intro q hq
      have hb := hBRbn q hq
      simp only at hb
      rw [Vbn q hq, Vbn (e.qbn / 2) ⟨by linarith, by linarith⟩] at hb
      constructor
      · intro h; have := hb.1 h; nlinarith
      · intro h; have := hb.2 h; nlinarith
    · intro _; positivity
    · intro h; rw [h]; linarith
  have ro : ∀ h : ℝ, 0 ≤ h → 1 * h ^ 2 + 3 * h = 9 * c + h ^ 2 / 4 + 3 * h / 2 →
      h = Real.sqrt (1 + 12 * c) - 1 := by
    intro h h0 hq
    have : Real.sqrt (1 + 12 * c) = h + 1 := by
      rw [Real.sqrt_eq_iff_eq_sq (by linarith) (by linarith)]
      nlinarith
    rw [this]; ring
  have rn : ∀ h : ℝ, 0 ≤ h → 1 * h ^ 2 + 1 * h = 9 * c + h ^ 2 / 4 + h / 2 →
      h = (Real.sqrt (1 + 108 * c) - 1) / 3 := by
    intro h h0 hq
    have : Real.sqrt (1 + 108 * c) = 3 * h + 1 := by
      rw [Real.sqrt_eq_iff_eq_sq (by linarith) (by linarith)]
      nlinarith
    rw [this]; ring
  exact ⟨ro _ hao0 eao, rn _ han0 ean, ro _ hbo0 ebo, rn _ hbn0 ebn⟩

lemma algU (c s : ℝ) (hs0 : 0 < s) (hs2 : s ^ 2 = 1 + 27 * c) :
    2 / 3 * (2 - c + c / s) * (1 / 2) +
      (((1 + 2 * (1 / 2 : ℝ)) ^ 2 + (3 - 4 * (1 / 2 : ℝ)) ^ 2) / 18
        + (2 - ((2 * s - 2) / 3) ^ 3 - ((2 * s - 2) / 3) ^ 3) / 108 - c * (1 - (2 * s - 2) / 3))
      = (718 - 1134 * c) / 729 - (16 - 189 * c - 10206 * c ^ 2) / (729 * s) := by
  have hc : c = (s ^ 2 - 1) / 27 := by linarith
  subst hc
  field_simp
  ring

lemma algB (c a d : ℝ) (ha0 : 0 < a) (hd0 : 0 < d) (ha2 : a ^ 2 = 1 + 12 * c)
    (hd2 : d ^ 2 = 1 + 108 * c) :
    (4 / 3 - c * (5 + 54 * c) / (3 * a) + c * (5 + 162 * c) / (3 * d)) * (1 / 2) +
      (((1 + 2 * (1 / 2 : ℝ)) ^ 2 + (3 - 4 * (1 / 2 : ℝ)) ^ 2) / 18
        + (4 - (a - 1) ^ 3 - ((d - 1) / 3) ^ 3 - (a - 1) ^ 3 - ((d - 1) / 3) ^ 3) / 216
        - c * (1 - 1 / 2 * (a - 1) - (1 - 1 / 2) * ((d - 1) / 3)))
      = (730 - 891 * c) / 729 - (1 + 24 * c + 117 * c ^ 2) / (27 * a)
          - (1 - 594 * c - 29889 * c ^ 2) / (729 * d) := by
  rw [← sub_eq_zero]
  have key : (4 / 3 - c * (5 + 54 * c) / (3 * a) + c * (5 + 162 * c) / (3 * d)) * (1 / 2) +
      (((1 + 2 * (1 / 2 : ℝ)) ^ 2 + (3 - 4 * (1 / 2 : ℝ)) ^ 2) / 18
        + (4 - (a - 1) ^ 3 - ((d - 1) / 3) ^ 3 - (a - 1) ^ 3 - ((d - 1) / 3) ^ 3) / 216
        - c * (1 - 1 / 2 * (a - 1) - (1 - 1 / 2) * ((d - 1) / 3)))
      - ((730 - 891 * c) / 729 - (1 + 24 * c + 117 * c ^ 2) / (27 * a)
          - (1 - 594 * c - 29889 * c ^ 2) / (729 * d))
      = ((-27 * d * (a ^ 2 - 3 * a - 42 * c + 4)) * (a ^ 2 - 1 - 12 * c)
          + (a * (378 * c - d ^ 2 + 3 * d - 4)) * (d ^ 2 - 1 - 108 * c)) / (2916 * a * d) := by
    field_simp
    ring
  rw [key, show a ^ 2 - 1 - 12 * c = 0 by linarith, show d ^ 2 - 1 - 108 * c = 0 by linarith]
  simp

lemma exAnteB_U_val (c x1 : ℝ) (hx0 : 0 < x1) (hx1 : x1 < 1) (e : ProfileU)
    (he : IsStage2EqU c x1 e) (hreg : SupportRegion1U x1 e) :
    exAnteB_U c x1 e =
      ((4 * x1 - 1) ^ 2 + (3 - 2 * x1) ^ 2) / 18 + (2 - e.qa ^ 3 - e.qb ^ 3) / 108
        - c * (1 - e.qb) := by
  obtain ⟨⟨hqa0, hqa1⟩, ⟨hqb0, hqb1⟩, hNA, hNB, -, -⟩ := he
  obtain ⟨hr1, hr2⟩ := hreg
  unfold exAnteB_U
  refine (dbl3 hqa0 hqa1 hqa0 hqa1 hqb0 hqb1 hqb0 hqb1 _
    (((4 * x1 - 1) ^ 2 + (3 - 2 * x1) ^ 2) / 18) (-(2 * ((4 * x1 - 1) + (3 - 2 * x1)) / 18))
    (2 * ((4 * x1 - 1) + (3 - 2 * x1)) / 18) (2 / 18) (-4 / 18) (2 / 18) 0 0 0 0 0 (-c) 0
    (fun x hx y hy => ?_)).trans ?_
  · obtain ⟨u1, u2⟩ := bel_bounds hqa0 hqa1 hx
    obtain ⟨w1, w2⟩ := bel_bounds hqb0 hqb1 hy
    have hA := nashA_val x1 _ _ _ hx0 (by linarith) (by linarith)
      (hNA _ ⟨by linarith, u2⟩ _ ⟨by linarith, w2⟩)
    have hB := nashB_val x1 _ _ _ hx1 (by linarith) (by linarith)
      (hNB _ ⟨by linarith, u2⟩ _ ⟨by linarith, w2⟩)
    have hA' : e.σA (bel e.qa x) (bel e.qb y) = ((1 + 2 * x1 + bel e.qa x - bel e.qb y) / 3,
        (4 * x1 - 1 - bel e.qa x + bel e.qb y) / 3) := Prod.ext hA.1 hA.2
    have hB' : e.σB (bel e.qa x) (bel e.qb y) = ((3 - 4 * x1 + bel e.qa x - bel e.qb y) / 3,
        (3 - 2 * x1 + bel e.qb y - bel e.qa x) / 3) := Prod.ext hB.1 hB.2
    rw [hA', hB', revBA_val _ _ _ (by linarith) (by linarith),
      revBB_val _ _ _ (by linarith) (by linarith), ite_ind]
    ring
  · ring

lemma exAnteB_BBD_val (c x1 : ℝ) (hx0 : 0 < x1) (hx1 : x1 < 1) (e : ProfileBBD)
    (he : IsStage2EqBBD c x1 e) (hreg : SupportRegion1BBD x1 e) :
    exAnteB_BBD c x1 e =
      ((4 * x1 - 1) ^ 2 + (3 - 2 * x1) ^ 2) / 18
        + (4 - e.qao ^ 3 - e.qan ^ 3 - e.qbo ^ 3 - e.qbn ^ 3) / 216
        - c * (x1 * (1 - e.qbn) + (1 - x1) * (1 - e.qbo)) := by
  obtain ⟨⟨hao0, hao1⟩, ⟨han0, han1⟩, ⟨hbo0, hbo1⟩, ⟨hbn0, hbn1⟩, hNA, hNB, -⟩ := he
  obtain ⟨hr1, hr2⟩ := hreg
  unfold exAnteB_BBD
  refine (dbl3 hao0 hao1 han0 han1 hbn0 hbn1 hbo0 hbo1 _
    (((4 * x1 - 1) ^ 2 + (3 - 2 * x1) ^ 2) / 18) (-(2 * (4 * x1 - 1) / 18)) (2 * (4 * x1 - 1) / 18)
    (1 / 18) (-2 / 18) (1 / 18) (-(2 * (3 - 2 * x1) / 18)) (2 * (3 - 2 * x1) / 18)
    (1 / 18) (-2 / 18) (1 / 18) (-(x1 * c)) (-((1 - x1) * c))
    (fun x hx y hy => ?_)).trans ?_
  · obtain ⟨u1, u2⟩ := bel_bounds hao0 hao1 hx
    obtain ⟨w1, w2⟩ := bel_bounds hbn0 hbn1 hy
    obtain ⟨u3, u4⟩ := bel_bounds han0 han1 hx
    obtain ⟨w3, w4⟩ := bel_bounds hbo0 hbo1 hy
    have hA := nashA_val x1 _ _ _ hx0 (by linarith) (by linarith)
      (hNA _ ⟨by linarith, u2⟩ _ ⟨by linarith, w2⟩)
    have hB := nashB_val x1 _ _ _ hx1 (by linarith) (by linarith)
      (hNB _ ⟨by linarith, u4⟩ _ ⟨by linarith, w4⟩)
    have hA' : e.σA (bel e.qao x) (bel e.qbn y) = ((1 + 2 * x1 + bel e.qao x - bel e.qbn y) / 3,
        (4 * x1 - 1 - bel e.qao x + bel e.qbn y) / 3) := Prod.ext hA.1 hA.2
    have hB' : e.σB (bel e.qan x) (bel e.qbo y) = ((3 - 4 * x1 + bel e.qan x - bel e.qbo y) / 3,
        (3 - 2 * x1 + bel e.qbo y - bel e.qan x) / 3) := Prod.ext hB.1 hB.2
    rw [hA', hB', revBA_val _ _ _ (by linarith) (by linarith),
      revBB_val _ _ _ (by linarith) (by linarith), ite_ind, ite_ind]
    ring
  · ring

end BBDAuxC

open BBDisclosure.Total

theorem solution (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) :
    (∀ s : SPE_U, IsSymSPE_U c s →
      totalA_U c s = (718 - 1134 * c) / 729
          - (16 - 189 * c - 10206 * c ^ 2) / (729 * Real.sqrt (1 + 27 * c)) ∧
      totalB_U c s = (718 - 1134 * c) / 729
          - (16 - 189 * c - 10206 * c ^ 2) / (729 * Real.sqrt (1 + 27 * c))) ∧
    (∀ s : SPE_BBD, IsSymSPE_BBD c s →
      totalA_BBD c s = (730 - 891 * c) / 729
          - (1 + 24 * c + 117 * c ^ 2) / (27 * Real.sqrt (1 + 12 * c))
          - (1 - 594 * c - 29889 * c ^ 2) / (729 * Real.sqrt (1 + 108 * c)) ∧
      totalB_BBD c s = (730 - 891 * c) / 729
          - (1 + 24 * c + 117 * c ^ 2) / (27 * Real.sqrt (1 + 12 * c))
          - (1 - 594 * c - 29889 * c ^ 2) / (729 * Real.sqrt (1 + 108 * c))) := by
  constructor
  · intro s hs
    obtain ⟨hp, hx⟩ := (equation_9 c hc0 hc).2 s hs
    have he := hs.2.1 (1 / 2) ⟨by norm_num, by norm_num⟩
    obtain ⟨hqa, hqb⟩ := BBDAuxC.thrU_half c hc0 hc _ he
    have hr1 : 1 < Real.sqrt (1 + 27 * c) := by
      rw [show (1 : ℝ) < Real.sqrt (1 + 27 * c) ↔ 1 ^ 2 < 1 + 27 * c from
        Real.lt_sqrt (by norm_num)]
      linarith
    have hr2 : Real.sqrt (1 + 27 * c) ^ 2 = 1 + 27 * c := Real.sq_sqrt (by linarith)
    have hreg : BBDisclosure.Stage2.SupportRegion1U (1 / 2) (s.stage2 (1 / 2)) :=
      ⟨by rw [hqb]; linarith, by rw [hqa]; linarith⟩
    have hA := equation_5 c (1 / 2) hc0 hc (by norm_num) (by norm_num) _ he hreg
    have hB := BBDAuxC.exAnteB_U_val c (1 / 2) (by norm_num) (by norm_num) _ he hreg
    unfold totalA_U totalB_U PiA_U PiB_U
    rw [hx, hA, hB, hp, hqa, hqb]
    have key := BBDAuxC.algU c (Real.sqrt (1 + 27 * c)) (by linarith) hr2
    constructor
    · linear_combination key
    · linear_combination key
  · intro s hs
    obtain ⟨hp, hx⟩ := (equation_17 c hc0 hc).2 s hs
    have he := hs.2.1 (1 / 2) ⟨by norm_num, by norm_num⟩
    obtain ⟨hao, han, hbo, hbn⟩ := BBDAuxC.thrB_half c hc0 hc _ he
    have ha1 : 1 < Real.sqrt (1 + 12 * c) := by
      rw [show (1 : ℝ) < Real.sqrt (1 + 12 * c) ↔ 1 ^ 2 < 1 + 12 * c from
        Real.lt_sqrt (by norm_num)]
      linarith
    have hd1 : 1 < Real.sqrt (1 + 108 * c) := by
      rw [show (1 : ℝ) < Real.sqrt (1 + 108 * c) ↔ 1 ^ 2 < 1 + 108 * c from
        Real.lt_sqrt (by norm_num)]
      linarith
    have ha2 : Real.sqrt (1 + 12 * c) ^ 2 = 1 + 12 * c := Real.sq_sqrt (by linarith)
    have hd2 : Real.sqrt (1 + 108 * c) ^ 2 = 1 + 108 * c := Real.sq_sqrt (by linarith)
    have hreg : BBDisclosure.Stage2.SupportRegion1BBD (1 / 2) (s.stage2 (1 / 2)) :=
      ⟨by rw [hbn]; linarith, by rw [han]; linarith⟩
    have hA := equation_14 c (1 / 2) hc0 hc (by norm_num) (by norm_num) _ he hreg
    have hB := BBDAuxC.exAnteB_BBD_val c (1 / 2) (by norm_num) (by norm_num) _ he hreg
    unfold totalA_BBD totalB_BBD PiA_BBD PiB_BBD
    rw [hx, hA, hB, hp, hao, han, hbo, hbn]
    have key := BBDAuxC.algB c (Real.sqrt (1 + 12 * c)) (Real.sqrt (1 + 108 * c))
      (by linarith) (by linarith) ha2 hd2
    constructor
    · linear_combination key
    · linear_combination key
