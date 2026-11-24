-- Prove2me | solution 1 for DelaunayStretch.lemma_5_8_reduction_H1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T03:18:36.075018+00:00
-- url     : https://prove2.me/submissions/2899d90a-cfe4-417f-8869-59cc031c7be7

import Mathlib
import Definitions.Def_DelaunayStretch_FamilyPieces
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

open DelaunayStretch

namespace L58

/-- The quintic in the clipped variable, with `|g'| ≤ k` from three Bernstein bounds. -/
theorem quintic_lipschitz (c σ m1 m2 k : ℝ)
    (h1 : |σ + m1| ≤ k) (h2 : |σ - m1 / 2 + 3 / 2 * m2| ≤ k) (h3 : |σ - 2 * m1 - 2 * m2| ≤ k)
    (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |(c + σ * x + (m1 * (x - x ^ 3) + m2 * (x ^ 3 - x ^ 5))) -
      (c + σ * y + (m1 * (y - y ^ 3) + m2 * (y ^ 3 - y ^ 5)))| ≤ k * |x - y| := by
  set g : ℝ → ℝ := fun t => c + σ * t + (m1 * (t - t ^ 3) + m2 * (t ^ 3 - t ^ 5)) with hg
  have hderiv : ∀ t, HasDerivAt g (σ + m1 * (1 - 3 * t ^ 2) + m2 * (3 * t ^ 2 - 5 * t ^ 4)) t := by
    intro t
    have h3 := hasDerivAt_pow 3 t
    have h5 := hasDerivAt_pow 5 t
    have hid := hasDerivAt_id' t
    have := ((hid.const_mul σ).const_add c).add (((hid.sub h3).const_mul m1).add
      ((h3.sub h5).const_mul m2))
    rw [hg]
    refine this.congr_deriv ?_
    push_cast; ring
  have hbound : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ‖σ + m1 * (1 - 3 * t ^ 2) + m2 * (3 * t ^ 2 - 5 * t ^ 4)‖ ≤ k := by
    intro t ht
    have hy0 : 0 ≤ t ^ 2 := sq_nonneg t
    have hy1 : t ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]; exact abs_le.mpr ⟨ht.1, ht.2⟩
    set u := t ^ 2 with hu
    have e : σ + m1 * (1 - 3 * t ^ 2) + m2 * (3 * t ^ 2 - 5 * t ^ 4) =
        (σ + m1) * (1 - u) ^ 2 + 2 * (σ - m1 / 2 + 3 / 2 * m2) * (u * (1 - u)) +
          (σ - 2 * m1 - 2 * m2) * u ^ 2 := by
      rw [hu]; ring
    rw [e, Real.norm_eq_abs]
    have w0 : 0 ≤ (1 - u) ^ 2 := sq_nonneg _
    have w1 : 0 ≤ u * (1 - u) := mul_nonneg hy0 (by linarith)
    have w2 : 0 ≤ u ^ 2 := sq_nonneg _
    have hsum : (1 - u) ^ 2 + 2 * (u * (1 - u)) + u ^ 2 = 1 := by ring
    obtain ⟨a1, a2⟩ := abs_le.mp h1
    obtain ⟨b1, b2⟩ := abs_le.mp h2
    obtain ⟨c1, c2⟩ := abs_le.mp h3
    rw [abs_le]; constructor <;> nlinarith [mul_le_mul_of_nonneg_left a1 w0,
      mul_le_mul_of_nonneg_left a2 w0, mul_le_mul_of_nonneg_left b1 w1,
      mul_le_mul_of_nonneg_left b2 w1, mul_le_mul_of_nonneg_left c1 w2,
      mul_le_mul_of_nonneg_left c2 w2]
  have hconv : Convex ℝ (Set.Icc (-1 : ℝ) 1) := convex_Icc _ _
  have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hderiv t).hasDerivWithinAt) hbound
    (show y ∈ Set.Icc (-1 : ℝ) 1 from ⟨(abs_le.mp hy).1, (abs_le.mp hy).2⟩)
    (show x ∈ Set.Icc (-1 : ℝ) 1 from ⟨(abs_le.mp hx).1, (abs_le.mp hx).2⟩)
  simpa [Real.norm_eq_abs, hg] using this

theorem clip_lip (x y : ℝ) : |clip 1 x - clip 1 y| ≤ |x - y| := by
  unfold clip
  rw [max_comm (-1), max_comm (-1)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

theorem abs_clip_le_one (x : ℝ) : |clip 1 x| ≤ 1 := by
  unfold clip; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem affine_bound (α β k Rb s : ℝ) (hRb : 0 ≤ Rb) (hs : |s| ≤ Rb)
    (h : ∀ t : ℝ, (t = Rb ∨ t = -Rb) → |α + β * t| ≤ k) : |α + β * s| ≤ k := by
  have hp := abs_le.mp (h Rb (Or.inl rfl))
  have hm := abs_le.mp (h (-Rb) (Or.inr rfl))
  obtain ⟨s1, s2⟩ := abs_le.mp hs
  rcases eq_or_lt_of_le hRb with h0 | hpos
  · have : s = 0 := by linarith
    subst this; rw [← h0] at hp; simpa using h Rb (Or.inl rfl) |>.trans_eq' (by rw [← h0]; simp)
  · rw [abs_le]; constructor
    · have : Rb * (-k) ≤ Rb * (α + β * s) := by
        nlinarith [mul_le_mul_of_nonneg_left hp.1 (by linarith : 0 ≤ Rb + s),
          mul_le_mul_of_nonneg_left hm.1 (by linarith : 0 ≤ Rb - s)]
      exact le_of_mul_le_mul_left this hpos
    · have : Rb * (α + β * s) ≤ Rb * k := by
        nlinarith [mul_le_mul_of_nonneg_left hp.2 (by linarith : 0 ≤ Rb + s),
          mul_le_mul_of_nonneg_left hm.2 (by linarith : 0 ≤ Rb - s)]
      exact le_of_mul_le_mul_left this hpos

theorem omega_facts (γ φ θ : ℝ) (h : (γ, φ, θ) ∈ OmegaSet) :
    |γ| < Real.pi / 2 ∧ 0 ≤ (θ - φ + γ) / (Real.pi + 2 * γ) ∧ (θ - φ + γ) / (Real.pi + 2 * γ) ≤ 1 ∧
      0 ≤ (θ + φ - γ) / (Real.pi - 2 * γ) ∧ (θ + φ - γ) / (Real.pi - 2 * γ) ≤ 1 := by
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  have hb1 := le_abs_self (γ - φ); have hb2 := neg_abs_le (γ - φ)
  have hc1 := le_abs_self (γ + φ); have hc2 := neg_abs_le (γ + φ)
  have hg : |γ| < Real.pi / 2 := by
    rw [abs_lt]; constructor <;> linarith
  obtain ⟨g1, g2⟩ := abs_lt.mp hg
  have p1 : 0 < Real.pi + 2 * γ := by linarith
  have p2 : 0 < Real.pi - 2 * γ := by linarith
  refine ⟨hg, ?_, ?_, ?_, ?_⟩
  · apply div_nonneg _ p1.le; linarith
  · rw [div_le_one p1]; linarith
  · apply div_nonneg _ p2.le; linarith
  · rw [div_le_one p2]; linarith

end L58

open L58

theorem pos_case (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (Rb : ℝ) (hRb : 0 ≤ Rb)
    (hR : ∀ γ a b : ℝ, 0 ≤ γ → γ ≤ Real.pi / 2 → 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      |familyR R γ a b| ≤ Rb)
    (h59 : ∀ γ : ℝ, 0 ≤ γ → γ < Real.pi / 2 → ∀ s : ℝ, (s = Rb ∨ s = -Rb) →
      |(γ - Real.cos γ ^ 2 * familyV V γ 0 1) + Real.cos γ ^ 2 * (familySpline Bc γ + s)| ≤
          Real.pi / 2 - Real.cos γ ∧
      |(γ - Real.cos γ ^ 2 * familyV V γ 0 1) - Real.cos γ ^ 2 * (familySpline Bc γ + s) / 2 +
          3 / 2 * (Real.cos γ ^ 2 * familySpline Dc γ)| ≤ Real.pi / 2 - Real.cos γ ∧
      |(γ - Real.cos γ ^ 2 * familyV V γ 0 1) - 2 * (Real.cos γ ^ 2 * (familySpline Bc γ + s)) -
          2 * (Real.cos γ ^ 2 * familySpline Dc γ)| ≤ Real.pi / 2 - Real.cos γ)
    (γ φ θ : ℝ) (hΩ : (γ, φ, θ) ∈ OmegaSet) (hγ : 0 ≤ γ) (ψ₁ ψ₂ : ℝ) :
    |familyHPos V R Bc Dc γ φ θ ψ₁ - familyHPos V R Bc Dc γ φ θ ψ₂| ≤ |ψ₁ - ψ₂| := by
  obtain ⟨hg, ha0, ha1, hb0, hb1⟩ := omega_facts γ φ θ hΩ
  have hγ2 : γ < Real.pi / 2 := (abs_lt.mp hg).2
  set a := (θ - φ + γ) / (Real.pi + 2 * γ)
  set b := (θ + φ - γ) / (Real.pi - 2 * γ)
  set k := Real.pi / 2 - Real.cos γ with hk
  have hkpos : 0 < k := by
    have := Real.cos_le_one γ; have := Real.pi_gt_three; rw [hk]; linarith
  set c2 := Real.cos γ ^ 2
  set σ := γ - c2 * familyV V γ 0 1
  set Rv := familyR R γ a b
  have hRv : |Rv| ≤ Rb := hR γ a b hγ hγ2.le ha0 ha1 hb0 hb1
  set m1 := c2 * (familySpline Bc γ + Rv)
  set m2 := c2 * familySpline Dc γ
  have H := h59 γ hγ hγ2
  have b1 : |σ + m1| ≤ k := by
    have := affine_bound (σ + c2 * familySpline Bc γ) c2 k Rb Rv hRb hRv
      (fun t ht => by
        have := (H t ht).1; convert this using 2; ring)
    convert this using 2; simp only [m1]; ring
  have b2 : |σ - m1 / 2 + 3 / 2 * m2| ≤ k := by
    have := affine_bound (σ - c2 * familySpline Bc γ / 2 + 3 / 2 * m2) (-(c2 / 2)) k Rb Rv hRb hRv
      (fun t ht => by
        have := (H t ht).2.1; convert this using 2; simp only [m2]; ring)
    convert this using 2; simp only [m1]; ring
  have b3 : |σ - 2 * m1 - 2 * m2| ≤ k := by
    have := affine_bound (σ - 2 * (c2 * familySpline Bc γ) - 2 * m2) (-(2 * c2)) k Rb Rv hRb hRv
      (fun t ht => by
        have := (H t ht).2.2; convert this using 2; simp only [m2]; ring)
    convert this using 2; simp only [m1]; ring
  have key := quintic_lipschitz (c2 * familyV V γ a b) σ m1 m2 k b1 b2 b3
    (clip 1 (ψ₁ / k)) (clip 1 (ψ₂ / k)) (abs_clip_le_one _) (abs_clip_le_one _)
  have e : ∀ ψ, familyHPos V R Bc Dc γ φ θ ψ =
      c2 * familyV V γ a b + σ * clip 1 (ψ / k) +
        (m1 * (clip 1 (ψ / k) - clip 1 (ψ / k) ^ 3) +
          m2 * (clip 1 (ψ / k) ^ 3 - clip 1 (ψ / k) ^ 5)) := by
    intro ψ; simp only [familyHPos]; ring
  rw [e, e]
  refine key.trans ?_
  have hc := clip_lip (ψ₁ / k) (ψ₂ / k)
  rw [← sub_div, abs_div, abs_of_pos hkpos] at hc
  calc k * |clip 1 (ψ₁ / k) - clip 1 (ψ₂ / k)| ≤ k * (|ψ₁ - ψ₂| / k) :=
        mul_le_mul_of_nonneg_left hc hkpos.le
    _ = |ψ₁ - ψ₂| := by field_simp

theorem solution (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (Rb : ℝ) (hRb : 0 ≤ Rb)
    (hR : ∀ γ a b : ℝ, 0 ≤ γ → γ ≤ Real.pi / 2 → 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      |familyR R γ a b| ≤ Rb)
    (h59 : ∀ γ : ℝ, 0 ≤ γ → γ < Real.pi / 2 → ∀ s : ℝ, (s = Rb ∨ s = -Rb) →
      |(γ - Real.cos γ ^ 2 * familyV V γ 0 1) + Real.cos γ ^ 2 * (familySpline Bc γ + s)| ≤
          Real.pi / 2 - Real.cos γ ∧
      |(γ - Real.cos γ ^ 2 * familyV V γ 0 1) - Real.cos γ ^ 2 * (familySpline Bc γ + s) / 2 +
          3 / 2 * (Real.cos γ ^ 2 * familySpline Dc γ)| ≤ Real.pi / 2 - Real.cos γ ∧
      |(γ - Real.cos γ ^ 2 * familyV V γ 0 1) - 2 * (Real.cos γ ^ 2 * (familySpline Bc γ + s)) -
          2 * (Real.cos γ ^ 2 * familySpline Dc γ)| ≤ Real.pi / 2 - Real.cos γ) :
    CondH1 (familyH V R Bc Dc) := by
  intro γ φ θ hΩ ψ₁ ψ₂
  simp only [familyH]
  by_cases hγ : 0 ≤ γ
  · rw [if_pos hγ, if_pos hγ]
    exact pos_case V R Bc Dc Rb hRb hR h59 γ φ θ hΩ hγ ψ₁ ψ₂
  · rw [if_neg hγ, if_neg hγ]
    have hΩ' : (-γ, -φ, θ) ∈ OmegaSet := by
      obtain ⟨h1, h2⟩ := hΩ
      refine ⟨?_, ?_⟩
      · show |-γ - -φ| < θ
        rw [show -γ - -φ = -(γ - φ) by ring, abs_neg]; exact h1
      · show θ < Real.pi - |-γ + -φ|
        rw [show -γ + -φ = -(γ + φ) by ring, abs_neg]; exact h2
    have := pos_case V R Bc Dc Rb hRb hR h59 (-γ) (-φ) θ hΩ' (by linarith) (-ψ₁) (-ψ₂)
    rwa [show -ψ₁ - -ψ₂ = -(ψ₁ - ψ₂) by ring, abs_neg] at this
