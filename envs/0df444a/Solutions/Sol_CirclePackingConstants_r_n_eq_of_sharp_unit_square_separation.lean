-- Prove2me | solution 1 for CirclePackingConstants.r_n_eq_of_sharp_unit_square_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T16:20:47.613808+00:00
-- url     : https://prove2.me/submissions/7e47b1d3-1e9c-451b-8193-5163a5e3138e

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

private def InUnitSquare (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

private lemma packable_zero (n : ℕ) : Packable n 0 := by
  refine ⟨le_rfl, by norm_num, (fun _ => (0, 0)), ?_, ?_⟩
  · intro i
    norm_num [InInnerSquare]
  · intro i j hij
    norm_num [sqDist]

private lemma admissible_radii_bddAbove (n : ℕ) :
    BddAbove {r : ℝ | Packable n r} := by
  refine ⟨1 / 2, ?_⟩
  intro r hr
  exact hr.2.1

private lemma r_n_eq_of_optimal {n : ℕ} {r : ℝ}
    (hr : Packable n r)
    (hupper : ∀ s, Packable n s → s ≤ r) : r_n n = r := by
  change sSup {s : ℝ | Packable n s} = r
  apply le_antisymm
  · exact csSup_le ⟨0, packable_zero n⟩ (fun s hs => hupper s hs)
  · exact le_csSup (admissible_radii_bddAbove n) hr

private lemma le_of_square_le {x b : ℝ}
    (hb : 0 ≤ b) (h : x ^ 2 ≤ b ^ 2) : x ≤ b := by
  by_contra hnot
  have h₁ : 0 < x - b := by linarith
  have h₂ : 0 < x + b := by linarith
  nlinarith only [h, mul_pos h₁ h₂]

private def NormalizedPackable (n : ℕ) (r : ℝ) : Prop :=
  0 ≤ r ∧ r ≤ 1 / 2 ∧
    ∃ p : Fin n → Point,
      (∀ i, InUnitSquare (p i)) ∧
      ∀ i j, i ≠ j →
        (2 * r) ^ 2 ≤ (1 - 2 * r) ^ 2 * sqDist (p i) (p j)

private lemma normalized_to_packable {n : ℕ} {r : ℝ}
    (h : NormalizedPackable n r) : Packable n r := by
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

private lemma packable_to_normalized {n : ℕ} {r : ℝ}
    (h : Packable n r) : NormalizedPackable n r := by
  rcases h with ⟨hr₀, hr₁, p, hp, hsep⟩
  by_cases hz : 1 - 2 * r = 0
  · refine ⟨hr₀, hr₁, (fun _ => (0, 0)), ?_, ?_⟩
    · intro i
      norm_num [InUnitSquare]
    · intro i j hij
      rcases hp i with ⟨hx₀, hx₁, hy₀, hy₁⟩
      rcases hp j with ⟨hx'₀, hx'₁, hy'₀, hy'₁⟩
      have hx : (p i).1 - (p j).1 = 0 := by linarith
      have hy : (p i).2 - (p j).2 = 0 := by linarith
      have hs := hsep i j hij
      simpa [sqDist, hx, hy, hz] using hs
  · have ha : 0 < 1 - 2 * r := by
      by_contra hnot
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

private lemma packable_of_separated_points {n : ℕ} {d : ℝ} (hd : 0 ≤ d)
    (p : Fin n → Point) (hp : ∀ i, InUnitSquare (p i))
    (hsep : ∀ i j, i ≠ j → d ^ 2 ≤ sqDist (p i) (p j)) :
    Packable n (d / (2 * (1 + d))) := by
  let r : ℝ := d / (2 * (1 + d))
  have hden : 0 < 2 * (1 + d) := by linarith
  have hne : 1 + d ≠ 0 := by linarith
  have hr₀ : 0 ≤ r := div_nonneg hd hden.le
  have hr₁ : r ≤ 1 / 2 := by
    dsimp [r]
    apply (div_le_iff₀ hden).2
    linarith
  have hid : (1 - 2 * r) * d = 2 * r := by
    dsimp [r]
    field_simp [hne]
    ring
  apply normalized_to_packable
  refine ⟨hr₀, hr₁, p, hp, ?_⟩
  intro i j hij
  calc
    (2 * r) ^ 2 = (1 - 2 * r) ^ 2 * d ^ 2 := by
      calc
        (2 * r) ^ 2 = ((1 - 2 * r) * d) ^ 2 :=
          congrArg (fun z : ℝ => z ^ 2) hid.symm
        _ = (1 - 2 * r) ^ 2 * d ^ 2 := by ring
    _ ≤ (1 - 2 * r) ^ 2 * sqDist (p i) (p j) :=
      mul_le_mul_of_nonneg_left (hsep i j hij) (sq_nonneg _)

private lemma packable_radius_le {n : ℕ} {d : ℝ} (hd : 0 ≤ d)
    (hbound : ∀ p : Fin n → Point, (∀ i, InUnitSquare (p i)) →
      ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ d ^ 2)
    {r : ℝ} (hr : Packable n r) : r ≤ d / (2 * (1 + d)) := by
  rcases packable_to_normalized hr with ⟨hr₀, hr₁, p, hp, hsep⟩
  rcases hbound p hp with ⟨i, j, hij, hdist⟩
  have hsq : (2 * r) ^ 2 ≤ ((1 - 2 * r) * d) ^ 2 := by
    calc
      (2 * r) ^ 2 ≤ (1 - 2 * r) ^ 2 * sqDist (p i) (p j) := hsep i j hij
      _ ≤ (1 - 2 * r) ^ 2 * d ^ 2 :=
        mul_le_mul_of_nonneg_left hdist (sq_nonneg _)
      _ = ((1 - 2 * r) * d) ^ 2 := by ring
  have hlin : 2 * r ≤ (1 - 2 * r) * d :=
    le_of_square_le (mul_nonneg (by linarith) hd) hsq
  have hden : 0 < 2 * (1 + d) := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith only [hlin]

theorem sharpUnitSquareSeparationProof {n : ℕ} {d : ℝ} (hd : 0 ≤ d)
    (hlower : ∃ p : Fin n → Point, (∀ i, InUnitSquare (p i)) ∧
      ∀ i j, i ≠ j → d ^ 2 ≤ sqDist (p i) (p j))
    (hupper : ∀ p : Fin n → Point, (∀ i, InUnitSquare (p i)) →
      ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ d ^ 2) :
    r_n n = d / (2 * (1 + d)) := by
  rcases hlower with ⟨p, hp, hsep⟩
  apply r_n_eq_of_optimal (packable_of_separated_points hd p hp hsep)
  intro r hr
  exact packable_radius_le hd hupper hr

end CirclePackingConstants

theorem solution {n : ℕ} {d : ℝ} (hd : 0 ≤ d)
    (hlower : ∃ p : Fin n → CirclePackingConstants.Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) ∧
      ∀ i j, i ≠ j → d ^ 2 ≤ CirclePackingConstants.sqDist (p i) (p j))
    (hupper : ∀ p : Fin n → CirclePackingConstants.Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
      ∃ i j, i ≠ j ∧ CirclePackingConstants.sqDist (p i) (p j) ≤ d ^ 2) :
    CirclePackingConstants.r_n n = d / (2 * (1 + d)) := by
  apply CirclePackingConstants.sharpUnitSquareSeparationProof hd
  · simpa [CirclePackingConstants.InUnitSquare] using hlower
  · simpa [CirclePackingConstants.InUnitSquare] using hupper
