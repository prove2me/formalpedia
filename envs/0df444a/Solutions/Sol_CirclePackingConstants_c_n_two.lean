-- Prove2me | solution 1 for CirclePackingConstants.c_n_two
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-12T11:05:20.872634+00:00
-- url     : https://prove2.me/submissions/364c20d9-275f-4fb5-86ff-78861e0bc5fa

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

/-- Membership in the unit square, used only inside this proof. -/
def InUnitSquare (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

lemma packable_zero (n : ℕ) : Packable n 0 := by
  refine ⟨le_rfl, by norm_num, (fun _ => (0, 0)), ?_, ?_⟩
  · intro i
    norm_num [InInnerSquare]
  · intro i j hij
    norm_num [sqDist]

lemma admissible_radii_bddAbove (n : ℕ) :
    BddAbove {r : ℝ | Packable n r} := by
  refine ⟨1 / 2, ?_⟩
  intro r hr
  exact hr.2.1

lemma r_n_nonneg (n : ℕ) : 0 ≤ r_n n := by
  exact le_csSup (admissible_radii_bddAbove n) (packable_zero n)

lemma r_n_le_half (n : ℕ) : r_n n ≤ 1 / 2 := by
  exact csSup_le ⟨0, packable_zero n⟩ (fun r hr => hr.2.1)

lemma r_n_eq_of_optimal {n : ℕ} {r : ℝ}
    (hr : Packable n r)
    (hupper : ∀ s, Packable n s → s ≤ r) : r_n n = r := by
  change sSup {s : ℝ | Packable n s} = r
  apply le_antisymm
  · exact csSup_le ⟨r, hr⟩ (fun s hs => hupper s hs)
  · exact le_csSup (admissible_radii_bddAbove n) hr

lemma sqDist_comm (p q : Point) : sqDist p q = sqDist q p := by
  unfold sqDist
  ring

/-- An elementary, explicitly certified square inequality. -/
private lemma square_le_of_bounds {x b : ℝ}
    (hl : -b ≤ x) (hu : x ≤ b) : x ^ 2 ≤ b ^ 2 := by
  have h₁ : 0 ≤ b - x := by linarith
  have h₂ : 0 ≤ b + x := by linarith
  nlinarith only [mul_nonneg h₁ h₂]

private lemma le_of_square_le {x b : ℝ}
    (hb : 0 ≤ b) (h : x ^ 2 ≤ b ^ 2) : x ≤ b := by
  by_contra hnot
  have h₁ : 0 < x - b := by linarith
  have h₂ : 0 < x + b := by linarith
  nlinarith only [h, mul_pos h₁ h₂]

private lemma unit_difference_sq_le {x y : ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1) : (x - y) ^ 2 ≤ 1 := by
  have h := square_le_of_bounds (x := x - y) (b := 1)
    (by linarith) (by linarith)
  simpa only [one_pow] using h

lemma unit_square_diameter {p q : Point}
    (hp : InUnitSquare p) (hq : InUnitSquare q) : sqDist p q ≤ 2 := by
  rcases hp with ⟨hx₀, hx₁, hy₀, hy₁⟩
  rcases hq with ⟨hx'₀, hx'₁, hy'₀, hy'₁⟩
  have hx := unit_difference_sq_le hx₀ hx₁ hx'₀ hx'₁
  have hy := unit_difference_sq_le hy₀ hy₁ hy'₀ hy'₁
  unfold sqDist
  linarith

/-! ## Normalizing the inner square

Both directions are proved, so the auxiliary point model does not restrict
which disk configurations are considered.
-/

def NormalizedPackable (n : ℕ) (r : ℝ) : Prop :=
  0 ≤ r ∧ r ≤ 1 / 2 ∧
    ∃ p : Fin n → Point,
      (∀ i, InUnitSquare (p i)) ∧
      ∀ i j, i ≠ j →
        (2 * r) ^ 2 ≤ (1 - 2 * r) ^ 2 * sqDist (p i) (p j)

lemma normalized_to_packable {n : ℕ} {r : ℝ}
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

lemma packable_to_normalized {n : ℕ} {r : ℝ}
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

lemma packable_iff_normalized (n : ℕ) (r : ℝ) :
    Packable n r ↔ NormalizedPackable n r :=
  ⟨packable_to_normalized, normalized_to_packable⟩

/-- A point configuration at separation `d` supplies an actual disk packing. -/
lemma packable_of_separated_points {n : ℕ} {d : ℝ} (hd : 0 ≤ d)
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

/-- Any universal point-separation obstruction bounds every disk radius. -/
lemma packable_radius_le {n : ℕ} {d : ℝ} (hd : 0 ≤ d)
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

lemma r_n_eq_of_sharp_separation {n : ℕ} {d : ℝ} (hd : 0 ≤ d)
    (hlower : ∃ p : Fin n → Point, (∀ i, InUnitSquare (p i)) ∧
      ∀ i j, i ≠ j → d ^ 2 ≤ sqDist (p i) (p j))
    (hupper : ∀ p : Fin n → Point, (∀ i, InUnitSquare (p i)) →
      ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ d ^ 2) :
    r_n n = d / (2 * (1 + d)) := by
  rcases hlower with ⟨p, hp, hsep⟩
  apply r_n_eq_of_optimal (packable_of_separated_points hd p hp hsep)
  intro r hr
  exact packable_radius_le hd hupper hr

/-! ## The two-point bound and witness -/

lemma two_point_lower :
    ∃ p : Fin 2 → Point, (∀ i, InUnitSquare (p i)) ∧
      ∀ i j, i ≠ j → (Real.sqrt 2) ^ 2 ≤ sqDist (p i) (p j) := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  refine ⟨![(0, 0), (1, 1)], ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [InUnitSquare]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [sqDist] <;> norm_num

lemma two_point_upper (p : Fin 2 → Point)
    (hp : ∀ i, InUnitSquare (p i)) :
    ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ (Real.sqrt 2) ^ 2 := by
  refine ⟨0, 1, by decide, ?_⟩
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact unit_square_diameter (hp 0) (hp 1)

lemma r_n_two_separation :
    r_n 2 = Real.sqrt 2 / (2 * (1 + Real.sqrt 2)) :=
  r_n_eq_of_sharp_separation (Real.sqrt_nonneg 2) two_point_lower two_point_upper

theorem r_n_two : r_n 2 = (2 - Real.sqrt 2) / 2 := by
  rw [r_n_two_separation]
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hne : 1 + Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hne]
  nlinarith only [hs]

end CirclePackingConstants

open CirclePackingConstants

theorem solution : c_n 2 = Real.pi * (3 - 2 * Real.sqrt 2) := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hc : 2 * ((2 - Real.sqrt 2) / 2) ^ 2 = 3 - 2 * Real.sqrt 2 := by
    nlinarith only [hs]
  simp only [c_n, r_n_two, Nat.cast_ofNat]
  calc
    2 * Real.pi * ((2 - Real.sqrt 2) / 2) ^ 2 =
        Real.pi * (2 * ((2 - Real.sqrt 2) / 2) ^ 2) := by ring
    _ = Real.pi * (3 - 2 * Real.sqrt 2) := by rw [hc]
