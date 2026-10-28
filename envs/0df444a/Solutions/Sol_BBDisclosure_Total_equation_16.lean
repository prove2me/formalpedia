-- Prove2me | solution 1 for BBDisclosure.Total.equation_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T22:59:43.224116+00:00
-- url     : https://prove2.me/submissions/2907478b-7fbd-40b8-ae9e-24662101f3e0

import Mathlib
import Definitions.Def_BBDisclosure_Total_Stage2
import Definitions.Def_BBDisclosure_Total_Game

namespace BBDAuxC

/-- clamp helper: `min L (max 0 t)` equals `t` when `0 ≤ t ≤ L`. -/
lemma clamp_eq {L t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ L) : min L (max 0 t) = t := by
  rw [max_eq_right h0, min_eq_right h1]

/-- Uniqueness of the Nash equilibrium of a turf price game. The incumbent charges `a`, the
poacher `b`; the incumbent's demand is `min L (max 0 ((K + b - a) / 2))` on a segment of length
`L`. If `0 ≤ K < 4L`, the only equilibrium in nonnegative prices is the interior one. -/
lemma turf_unique (K L a b : ℝ) (hL : 0 < L) (hK0 : 0 ≤ K) (hK : K < 4 * L) (ha : 0 ≤ a)
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
  · exfalso
    have hD : min L (max 0 z) = L := by rw [max_eq_right (by linarith), min_eq_left hzL]
    rcases lt_or_ge 0 (a + 2 * L - K) with h2 | h2
    · have h := hB ((a + 2 * L - K) / 2) (by linarith)
      rw [hD, sub_self, mul_zero] at h
      have : min L (max 0 ((K + (a + 2 * L - K) / 2 - a) / 2)) < L := by
        apply min_lt_of_right_lt
        apply max_lt hL
        linarith
      have : 0 < (a + 2 * L - K) / 2 * (L - min L (max 0 ((K + (a + 2 * L - K) / 2 - a) / 2))) := by
        apply mul_pos (by linarith) (by linarith)
      linarith
    · -- a ≤ K - 2L; the incumbent gains by charging K/2
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
      · rw [min_eq_left h4] at h3
        nlinarith
      · rw [min_eq_right h4] at h3
        nlinarith [sq_nonneg (K - 4 * L)]
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
    (hK : 1 + u - w < 4 * x1) (h : IsTurfNashA x1 u w p) :
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
    (hK : 1 + w - u < 4 * (1 - x1)) (h : IsTurfNashB x1 u w p) :
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

end BBDAuxC

open BBDisclosure.Stage2 in
theorem solution (c : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) (stage2 : ℝ → BBDisclosure.Stage2.ProfileBBD)
    (pa1 pb1 x1 : ℝ) (hpa : 0 ≤ pa1) (hpb : 0 ≤ pb1) (hx0 : 0 < x1) (hx1 : x1 < 1)
    (heq : BBDisclosure.Stage2.IsStage2EqBBD c x1 (stage2 x1)) (hreg : BBDisclosure.Stage2.SupportRegion1BBD x1 (stage2 x1))
    (hshare : BBDisclosure.Total.IsShareBBD stage2 pa1 pb1 x1) :
    x1 = 1 / 2 + 3 * (pb1 - pa1) / 8 := by
  obtain ⟨⟨hao0, hao1⟩, ⟨han0, han1⟩, ⟨hbo0, hbo1⟩, ⟨hbn0, hbn1⟩, hNA, hNB, -⟩ := heq
  obtain ⟨hr1, hr2⟩ := hreg
  have hsh := hshare.2.1 hx0 hx1
  set e := stage2 x1 with he
  have vA : ∀ x ∈ Set.uIcc (0 : ℝ) 1, ∀ y ∈ Set.uIcc (0 : ℝ) 1, e.σA (bel e.qao x) (bel e.qbn y) =
      ((1 + 2 * x1 + bel e.qao x - bel e.qbn y) / 3, (4 * x1 - 1 - bel e.qao x + bel e.qbn y) / 3) := by
    intro x hx y hy
    obtain ⟨u1, u2⟩ := BBDAuxC.bel_bounds hao0 hao1 hx
    obtain ⟨w1, w2⟩ := BBDAuxC.bel_bounds hbn0 hbn1 hy
    have := BBDAuxC.nashA_val x1 _ _ _ hx0 (by linarith) (by linarith)
      (hNA _ ⟨by linarith, u2⟩ _ ⟨by linarith, w2⟩)
    exact Prod.ext this.1 this.2
  have vB : ∀ x ∈ Set.uIcc (0 : ℝ) 1, ∀ y ∈ Set.uIcc (0 : ℝ) 1, e.σB (bel e.qan x) (bel e.qbo y) =
      ((3 - 4 * x1 + bel e.qan x - bel e.qbo y) / 3, (3 - 2 * x1 + bel e.qbo y - bel e.qan x) / 3) := by
    intro x hx y hy
    obtain ⟨u1, u2⟩ := BBDAuxC.bel_bounds han0 han1 hx
    obtain ⟨w1, w2⟩ := BBDAuxC.bel_bounds hbo0 hbo1 hy
    have := BBDAuxC.nashB_val x1 _ _ _ hx1 (by linarith) (by linarith)
      (hNB _ ⟨by linarith, u2⟩ _ ⟨by linarith, w2⟩)
    exact Prod.ext this.1 this.2
  have E1 : BBDisclosure.Total.EsurBn e = 1 / 2 - (4 * x1 - 1) / 3 := by
    unfold BBDisclosure.Total.EsurBn
    refine (BBDAuxC.dbl2 hao0 hao1 hao0 hao1 hbn0 hbn1 hbn0 hbn1 _
      (-(4 * x1 - 1) / 3) (1 / 3) (2 / 3) 0 0 0 0 0 0 0 0 0 0 (fun x hx y hy => ?_)).trans ?_
    · rw [vA x hx y hy]; ring
    · ring
  have E2 : BBDisclosure.Total.EsurAo e = 1 / 2 - (1 + 2 * x1) / 3 := by
    unfold BBDisclosure.Total.EsurAo
    refine (BBDAuxC.dbl2 hao0 hao1 hao0 hao1 hbn0 hbn1 hbn0 hbn1 _
      (-(1 + 2 * x1) / 3) (2 / 3) (1 / 3) 0 0 0 0 0 0 0 0 0 0 (fun x hx y hy => ?_)).trans ?_
    · rw [vA x hx y hy]; ring
    · ring
  have E3 : BBDisclosure.Total.EsurAn e = 1 / 2 - (3 - 4 * x1) / 3 := by
    unfold BBDisclosure.Total.EsurAn
    refine (BBDAuxC.dbl2 han0 han1 han0 han1 hbo0 hbo1 hbo0 hbo1 _
      (-(3 - 4 * x1) / 3) (2 / 3) (1 / 3) 0 0 0 0 0 0 0 0 0 0 (fun x hx y hy => ?_)).trans ?_
    · rw [vB x hx y hy]; ring
    · ring
  have E4 : BBDisclosure.Total.EsurBo e = 1 / 2 - (3 - 2 * x1) / 3 := by
    unfold BBDisclosure.Total.EsurBo
    refine (BBDAuxC.dbl2 han0 han1 han0 han1 hbo0 hbo1 hbo0 hbo1 _
      (-(3 - 2 * x1) / 3) (1 / 3) (2 / 3) 0 0 0 0 0 0 0 0 0 0 (fun x hx y hy => ?_)).trans ?_
    · rw [vB x hx y hy]; ring
    · ring
  unfold BBDisclosure.Total.lhs15 BBDisclosure.Total.rhs15 at hsh
  rw [E1, E2, E3, E4] at hsh
  rw [max_eq_left (by linarith), max_eq_left (by linarith)] at hsh
  linarith
