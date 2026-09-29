-- Prove2me | solution 1 for CirclePackingConstants.r_n_seven_upper
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T17:33:21.851026+00:00
-- url     : https://prove2.me/submissions/9af7cc34-82e0-4c89-98f0-15d82c606460

import Definitions.Def_CirclePackingConstants
import Theorems.Thm_CirclePackingConstants_seven_unit_square_close_pair

noncomputable section

open CirclePackingConstants

def InUnitSquareN7 (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

def NormalizedPackableN7 (n : ℕ) (r : ℝ) : Prop :=
  0 ≤ r ∧ r ≤ 1 / 2 ∧
    ∃ p : Fin n → Point,
      (∀ i, InUnitSquareN7 (p i)) ∧
      ∀ i j, i ≠ j →
        (2 * r) ^ 2 ≤ (1 - 2 * r) ^ 2 * sqDist (p i) (p j)

private lemma square_le_of_bounds_n7 {x b : ℝ}
    (hl : -b ≤ x) (hu : x ≤ b) : x ^ 2 ≤ b ^ 2 := by
  have h₁ : 0 ≤ b - x := by linarith
  have h₂ : 0 ≤ b + x := by linarith
  nlinarith only [mul_nonneg h₁ h₂]

private lemma le_of_square_le_n7 {x b : ℝ}
    (hb : 0 ≤ b) (h : x ^ 2 ≤ b ^ 2) : x ≤ b := by
  by_contra hnot
  have h₁ : 0 < x - b := by linarith
  have h₂ : 0 < x + b := by linarith
  nlinarith only [h, mul_pos h₁ h₂]

private lemma normalized_to_packable_n7 {n : ℕ} {r : ℝ}
    (h : NormalizedPackableN7 n r) : Packable n r := by
  rcases h with ⟨hr₀, hr₁, p, hp, hsep⟩
  let q : Fin n → Point := fun i =>
    (r + (1 - 2 * r) * (p i).1, r + (1 - 2 * r) * (p i).2)
  have ha : 0 ≤ 1 - 2 * r := by linarith
  refine ⟨hr₀, hr₁, q, ?_, ?_⟩
  · intro i
    rcases hp i with ⟨hx₀, hx₁, hy₀, hy₁⟩
    change r ≤ r + (1 - 2 * r) * (p i).1 ∧
      r + (1 - 2 * r) * (p i).1 ≤ 1 - r ∧
      r ≤ r + (1 - 2 * r) * (p i).2 ∧
      r + (1 - 2 * r) * (p i).2 ≤ 1 - r
    have hxlow := mul_nonneg ha hx₀
    have hxhigh := mul_nonneg ha (sub_nonneg.mpr hx₁)
    have hylow := mul_nonneg ha hy₀
    have hyhigh := mul_nonneg ha (sub_nonneg.mpr hy₁)
    constructor
    · nlinarith only [hxlow]
    constructor
    · nlinarith only [hxhigh]
    constructor
    · nlinarith only [hylow]
    · nlinarith only [hyhigh]
  · intro i j hij
    have hscale : sqDist (q i) (q j) =
        (1 - 2 * r) ^ 2 * sqDist (p i) (p j) := by
      dsimp [q, sqDist]
      ring
    rw [hscale]
    exact hsep i j hij

private lemma packable_to_normalized_n7 {n : ℕ} {r : ℝ}
    (h : Packable n r) : NormalizedPackableN7 n r := by
  rcases h with ⟨hr₀, hr₁, p, hp, hsep⟩
  by_cases hz : 1 - 2 * r = 0
  · refine ⟨hr₀, hr₁, (fun _ => (0, 0)), ?_, ?_⟩
    · intro i
      norm_num [InUnitSquareN7]
    · intro i j hij
      rcases hp i with ⟨hx₀, hx₁, hy₀, hy₁⟩
      rcases hp j with ⟨hx'₀, hx'₁, hy'₀, hy'₁⟩
      have hx : (p i).1 - (p j).1 = 0 := by linarith
      have hy : (p i).2 - (p j).2 = 0 := by linarith
      have hs := hsep i j hij
      simpa [sqDist, hx, hy, hz] using hs
  · have ha : 0 < 1 - 2 * r := by
      by_contra hnot
      have hnonpos : 1 - 2 * r ≤ 0 := le_of_not_gt hnot
      apply hz
      linarith
    let q : Fin n → Point := fun i =>
      (((p i).1 - r) / (1 - 2 * r), ((p i).2 - r) / (1 - 2 * r))
    refine ⟨hr₀, hr₁, q, ?_, ?_⟩
    · intro i
      rcases hp i with ⟨hx₀, hx₁, hy₀, hy₁⟩
      change 0 ≤ ((p i).1 - r) / (1 - 2 * r) ∧
        ((p i).1 - r) / (1 - 2 * r) ≤ 1 ∧
        0 ≤ ((p i).2 - r) / (1 - 2 * r) ∧
        ((p i).2 - r) / (1 - 2 * r) ≤ 1
      refine ⟨div_nonneg (by linarith) ha.le, ?_,
        div_nonneg (by linarith) ha.le, ?_⟩
      · apply (div_le_iff₀ ha).2
        linarith
      · apply (div_le_iff₀ ha).2
        linarith
    · intro i j hij
      have hscale : (1 - 2 * r) ^ 2 * sqDist (q i) (q j) =
          sqDist (p i) (p j) := by
        dsimp [q, sqDist]
        field_simp [hz]
        ring
      rw [hscale]
      exact hsep i j hij

private lemma packable_radius_le_n7 {n : ℕ} {d : ℝ} (hd : 0 ≤ d)
    (hbound : ∀ p : Fin n → Point, (∀ i, InUnitSquareN7 (p i)) →
      ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ d ^ 2)
    {r : ℝ} (hr : Packable n r) : r ≤ d / (2 * (1 + d)) := by
  rcases packable_to_normalized_n7 hr with ⟨hr₀, hr₁, p, hp, hsep⟩
  rcases hbound p hp with ⟨i, j, hij, hdist⟩
  have hsq : (2 * r) ^ 2 ≤ ((1 - 2 * r) * d) ^ 2 := by
    calc
      (2 * r) ^ 2 ≤ (1 - 2 * r) ^ 2 * sqDist (p i) (p j) := hsep i j hij
      _ ≤ (1 - 2 * r) ^ 2 * d ^ 2 :=
        mul_le_mul_of_nonneg_left hdist (sq_nonneg _)
      _ = ((1 - 2 * r) * d) ^ 2 := by ring
  have hlin : 2 * r ≤ (1 - 2 * r) * d :=
    le_of_square_le_n7 (mul_nonneg (by linarith) hd) hsq
  have hden : 0 < 2 * (1 + d) := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith only [hlin]

private lemma r_n_upper_of_close_pair_n7 {n : ℕ} {d : ℝ} (hd : 0 ≤ d)
    (hbound : ∀ p : Fin n → Point, (∀ i, InUnitSquareN7 (p i)) →
      ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ d ^ 2) :
    r_n n ≤ d / (2 * (1 + d)) := by
  change sSup {r : ℝ | Packable n r} ≤ d / (2 * (1 + d))
  refine csSup_le ⟨0, ?_⟩ ?_
  · refine ⟨le_rfl, by norm_num, (fun _ => (0, 0)), ?_, ?_⟩
    · intro i
      norm_num [InInnerSquare]
    · intro i j hij
      norm_num [sqDist]
  · intro r hr
    exact packable_radius_le_n7 hd hbound hr

theorem solution :
    r_n 7 ≤ (4 - 2 * Real.sqrt 3) /
      (2 * (1 + (4 - 2 * Real.sqrt 3))) := by
  let s : ℝ := 4 - 2 * Real.sqrt 3
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hbound : ∀ p : Fin 7 → Point, (∀ i, InUnitSquareN7 (p i)) →
      ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ s ^ 2 := by
    intro p hp
    have h := seven_unit_square_close_pair p (by
      intro i
      exact hp i)
    simpa [s] using h
  have hupper : r_n 7 ≤ s / (2 * (1 + s)) := by
    exact r_n_upper_of_close_pair_n7 hs_nonneg hbound
  simpa [s] using hupper

