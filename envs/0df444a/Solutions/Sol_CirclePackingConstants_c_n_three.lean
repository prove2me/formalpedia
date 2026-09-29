-- Prove2me | solution 1 for CirclePackingConstants.c_n_three
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-12T11:05:21.75749+00:00
-- url     : https://prove2.me/submissions/253c42af-41fa-459d-b8cb-7022cef9dcec

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

theorem c_n_two : c_n 2 = Real.pi * (3 - 2 * Real.sqrt 2) := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hc : 2 * ((2 - Real.sqrt 2) / 2) ^ 2 = 3 - 2 * Real.sqrt 2 := by
    nlinarith only [hs]
  simp only [c_n, r_n_two, Nat.cast_ofNat]
  calc
    2 * Real.pi * ((2 - Real.sqrt 2) / 2) ^ 2 =
        Real.pi * (2 * ((2 - Real.sqrt 2) / 2) ^ 2) := by ring
    _ = Real.pi * (3 - 2 * Real.sqrt 2) := by rw [hc]

/-! ## A coordinate proof of the sharp three-point upper bound

Put `s = sqrt 3 - 1`, `t = 2 - sqrt 3`, and `D = 8 - 4 * sqrt 3`.
Then `s+t=1`, `2*s>1`, and `D = 2*s^2 = 1+t^2`.

Suppose all three squared distances exceed `D`, and order their x coordinates.
Each adjacent x gap must exceed `t`, because every squared y gap is at most 1.
Consequently each adjacent x gap is at most `s`, forcing both adjacent absolute
y gaps to exceed `s`. The two endpoint y coordinates must then be within `t`.
Their squared Euclidean distance is at most `1+t^2=D`, a contradiction.
-/

private lemma far_difference {a b s : ℝ} (h : s ^ 2 < (a - b) ^ 2) :
    s < a - b ∨ s < b - a := by
  by_cases hab : s < a - b
  · exact Or.inl hab
  · right
    by_contra hba
    have hsq := square_le_of_bounds (x := a - b) (b := s)
      (by linarith) (by linarith)
    linarith

private lemma endpoints_close {a b c s t : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (hst : s + t = 1) (hs : 1 < 2 * s)
    (hab : s ^ 2 < (a - b) ^ 2) (hbc : s ^ 2 < (b - c) ^ 2) :
    (a - c) ^ 2 ≤ t ^ 2 := by
  rcases far_difference hab with hab | hab
  · rcases far_difference hbc with hbc | hbc
    · exfalso
      linarith
    · apply square_le_of_bounds <;> linarith
  · rcases far_difference hbc with hbc | hbc
    · apply square_le_of_bounds <;> linarith
    · exfalso
      linarith

private lemma ordered_three_impossible {a b c : Point} {s t D : ℝ}
    (ha : InUnitSquare a) (hb : InUnitSquare b) (hc : InUnitSquare c)
    (_hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (hsbig : 1 < 2 * s) (hD₁ : D = 1 + t ^ 2) (hD₂ : D = 2 * s ^ 2)
    (hxab : a.1 ≤ b.1) (hxbc : b.1 ≤ c.1)
    (hab : D < sqDist a b) (hbc : D < sqDist b c) (hac : D < sqDist a c) :
    False := by
  rcases ha with ⟨ax₀, ax₁, ay₀, ay₁⟩
  rcases hb with ⟨bx₀, bx₁, by₀, by₁⟩
  rcases hc with ⟨cx₀, cx₁, cy₀, cy₁⟩
  have hyab := unit_difference_sq_le ay₀ ay₁ by₀ by₁
  have hybc := unit_difference_sq_le by₀ by₁ cy₀ cy₁
  have hx₁ : t < b.1 - a.1 := by
    by_contra hnot
    have hsq := square_le_of_bounds (x := a.1 - b.1) (b := t)
      (by linarith) (by linarith)
    dsimp only [sqDist] at hab
    nlinarith only [hab, hsq, hyab, hD₁]
  have hx₂ : t < c.1 - b.1 := by
    by_contra hnot
    have hsq := square_le_of_bounds (x := b.1 - c.1) (b := t)
      (by linarith) (by linarith)
    dsimp only [sqDist] at hbc
    nlinarith only [hbc, hsq, hybc, hD₁]
  have hxab' : (a.1 - b.1) ^ 2 ≤ s ^ 2 :=
    square_le_of_bounds (by linarith) (by linarith)
  have hxbc' : (b.1 - c.1) ^ 2 ≤ s ^ 2 :=
    square_le_of_bounds (by linarith) (by linarith)
  have hy₁ : s ^ 2 < (a.2 - b.2) ^ 2 := by
    dsimp only [sqDist] at hab
    nlinarith only [hab, hxab', hD₂]
  have hy₂ : s ^ 2 < (b.2 - c.2) ^ 2 := by
    dsimp only [sqDist] at hbc
    nlinarith only [hbc, hxbc', hD₂]
  have hyac := endpoints_close ay₀ ay₁ by₀ by₁ cy₀ cy₁ hst hsbig hy₁ hy₂
  have hxac := unit_difference_sq_le ax₀ ax₁ cx₀ cx₁
  dsimp only [sqDist] at hac
  nlinarith only [hac, hyac, hxac, hD₁]

private lemma three_point_bound_param {a b c : Point} {s t D : ℝ}
    (ha : InUnitSquare a) (hb : InUnitSquare b) (hc : InUnitSquare c)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (hsbig : 1 < 2 * s) (hD₁ : D = 1 + t ^ 2) (hD₂ : D = 2 * s ^ 2) :
    sqDist a b ≤ D ∨ sqDist b c ≤ D ∨ sqDist a c ≤ D := by
  by_contra hnot
  have hab : D < sqDist a b := by
    by_contra h
    exact hnot (Or.inl (le_of_not_gt h))
  have hbc : D < sqDist b c := by
    by_contra h
    exact hnot (Or.inr (Or.inl (le_of_not_gt h)))
  have hac : D < sqDist a c := by
    by_contra h
    exact hnot (Or.inr (Or.inr (le_of_not_gt h)))
  have hba : D < sqDist b a := by simpa only [sqDist_comm b a] using hab
  have hcb : D < sqDist c b := by simpa only [sqDist_comm c b] using hbc
  have hca : D < sqDist c a := by simpa only [sqDist_comm c a] using hac
  by_cases h₁ : a.1 ≤ b.1
  · by_cases h₂ : b.1 ≤ c.1
    · exact ordered_three_impossible ha hb hc hs ht hst hsbig hD₁ hD₂
        h₁ h₂ hab hbc hac
    · by_cases h₃ : a.1 ≤ c.1
      · exact ordered_three_impossible ha hc hb hs ht hst hsbig hD₁ hD₂
          h₃ (lt_of_not_ge h₂).le hac hcb hab
      · exact ordered_three_impossible hc ha hb hs ht hst hsbig hD₁ hD₂
          (lt_of_not_ge h₃).le h₁ hca hab hcb
  · by_cases h₂ : a.1 ≤ c.1
    · exact ordered_three_impossible hb ha hc hs ht hst hsbig hD₁ hD₂
        (lt_of_not_ge h₁).le h₂ hba hac hbc
    · by_cases h₃ : b.1 ≤ c.1
      · exact ordered_three_impossible hb hc ha hs ht hst hsbig hD₁ hD₂
          h₃ (lt_of_not_ge h₂).le hbc hca hba
      · exact ordered_three_impossible hc hb ha hs ht hst hsbig hD₁ hD₂
          (lt_of_not_ge h₃).le (lt_of_not_ge h₁).le hcb hba hca

private lemma sqrt_three_bounds :
    (3 / 2 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 2 := by
  have hq₀ := Real.sqrt_nonneg (3 : ℝ)
  have hq₂ : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  constructor
  · by_contra hnot
    have h := square_le_of_bounds (x := Real.sqrt 3) (b := 3 / 2)
      (by linarith) (by linarith)
    nlinarith only [h, hq₂]
  · by_contra hnot
    have h := square_le_of_bounds (x := (2 : ℝ)) (b := Real.sqrt 3)
      (by linarith) (by linarith)
    nlinarith only [h, hq₂]

/-- The exact optimal three-point separation. -/
def delta_three : ℝ := Real.sqrt (8 - 4 * Real.sqrt 3)

lemma delta_three_nonneg : 0 ≤ delta_three := Real.sqrt_nonneg _

lemma delta_three_sq : delta_three ^ 2 = 8 - 4 * Real.sqrt 3 := by
  apply Real.sq_sqrt
  have h := sqrt_three_bounds.2
  linarith

lemma three_point_bound {a b c : Point}
    (ha : InUnitSquare a) (hb : InUnitSquare b) (hc : InUnitSquare c) :
    sqDist a b ≤ delta_three ^ 2 ∨
      sqDist b c ≤ delta_three ^ 2 ∨ sqDist a c ≤ delta_three ^ 2 := by
  have hq₂ : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  rcases sqrt_three_bounds with ⟨hqlo, hqhi⟩
  simp only [delta_three_sq]
  apply three_point_bound_param (s := Real.sqrt 3 - 1) (t := 2 - Real.sqrt 3)
    ha hb hc
  · linarith
  · linarith
  · ring
  · linarith
  · nlinarith only [hq₂]
  · nlinarith only [hq₂]

lemma three_point_lower :
    ∃ p : Fin 3 → Point, (∀ i, InUnitSquare (p i)) ∧
      ∀ i j, i ≠ j → delta_three ^ 2 ≤ sqDist (p i) (p j) := by
  rcases sqrt_three_bounds with ⟨hqlo, hqhi⟩
  refine ⟨![(1, 1), (Real.sqrt 3 - 1, 0), (0, Real.sqrt 3 - 1)], ?_, ?_⟩
  · intro i
    fin_cases i
    · norm_num [InUnitSquare]
    · change 0 ≤ Real.sqrt 3 - 1 ∧ Real.sqrt 3 - 1 ≤ 1 ∧
        0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1
      exact ⟨by linarith, by linarith, le_rfl, by norm_num⟩
    · change 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 ∧
        0 ≤ Real.sqrt 3 - 1 ∧ Real.sqrt 3 - 1 ≤ 1
      exact ⟨le_rfl, by norm_num, by linarith, by linarith⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [sqDist, delta_three_sq] <;>
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

lemma three_point_upper (p : Fin 3 → Point)
    (hp : ∀ i, InUnitSquare (p i)) :
    ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ delta_three ^ 2 := by
  rcases three_point_bound (hp 0) (hp 1) (hp 2) with h | h | h
  · exact ⟨0, 1, by decide, h⟩
  · exact ⟨1, 2, by decide, h⟩
  · exact ⟨0, 2, by decide, h⟩

lemma r_n_three_separation :
    r_n 3 = delta_three / (2 * (1 + delta_three)) :=
  r_n_eq_of_sharp_separation delta_three_nonneg three_point_lower three_point_upper

/-- Conversion to the radical expression used in the source notes. -/
lemma delta_three_eq_radicals : delta_three = Real.sqrt 6 - Real.sqrt 2 := by
  have h₂₀ := Real.sqrt_nonneg (2 : ℝ)
  have h₃₀ := Real.sqrt_nonneg (3 : ℝ)
  have h₆₀ := Real.sqrt_nonneg (6 : ℝ)
  have h₂ : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h₃ : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have h₆ : (Real.sqrt 6) ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  have hprod_sq : (Real.sqrt 2 * Real.sqrt 3) ^ 2 = (6 : ℝ) := by
    rw [mul_pow, h₂, h₃]
    norm_num
  have hprod : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    apply le_antisymm
    · exact le_of_square_le (mul_nonneg h₂₀ h₃₀)
        (le_of_eq (h₆.trans hprod_sq.symm))
    · exact le_of_square_le h₆₀
        (le_of_eq (hprod_sq.trans h₆.symm))
  have hs₀ : 0 ≤ Real.sqrt 3 - 1 := by
    have h := sqrt_three_bounds.1
    linarith
  have hs₂ : (Real.sqrt 3 - 1) ^ 2 = 4 - 2 * Real.sqrt 3 := by
    nlinarith only [h₃]
  have hv₂ : (Real.sqrt 2 * (Real.sqrt 3 - 1)) ^ 2 =
      8 - 4 * Real.sqrt 3 := by
    rw [mul_pow, h₂, hs₂]
    ring
  have hval : delta_three = Real.sqrt 2 * (Real.sqrt 3 - 1) := by
    apply le_antisymm
    · exact le_of_square_le (mul_nonneg h₂₀ hs₀)
        (le_of_eq (delta_three_sq.trans hv₂.symm))
    · exact le_of_square_le delta_three_nonneg
        (le_of_eq (hv₂.trans delta_three_sq.symm))
  rw [hval, hprod]
  ring

theorem r_n_three : r_n 3 =
    (Real.sqrt 6 - Real.sqrt 2) / (2 * (1 + (Real.sqrt 6 - Real.sqrt 2))) := by
  rw [r_n_three_separation, delta_three_eq_radicals]

end CirclePackingConstants

open CirclePackingConstants

theorem solution : c_n 3 =
    3 * Real.pi *
      ((Real.sqrt 6 - Real.sqrt 2) / (2 * (1 + (Real.sqrt 6 - Real.sqrt 2)))) ^ 2 := by
  simp only [c_n, r_n_three, Nat.cast_ofNat]
