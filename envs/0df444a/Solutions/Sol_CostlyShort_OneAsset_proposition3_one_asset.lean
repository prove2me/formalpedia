-- Prove2me | solution 1 for CostlyShort.OneAsset.proposition3_one_asset
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T09:30:56.150992+00:00
-- url     : https://prove2.me/submissions/dd5c9cfa-41da-4255-9a29-c085a6182b4d

import Mathlib
import Definitions.Def_CostlyShort_OneAsset_Setting

set_option autoImplicit false

namespace CostlyShort.OneAsset

noncomputable def p3Rf (σ s δ : ℝ) : ℝ := Real.sqrt (s ^ 2 * (1 - s) ^ 2 * δ ^ 2 + 4 * σ ^ 4 * s)

noncomputable def p3Ff (σ s δ : ℝ) : ℝ := (s * (1 - s) * δ - 2 * σ ^ 2 + p3Rf σ s δ) / (2 * (1 - s))

noncomputable def p3Gf (σ s δ : ℝ) : ℝ :=
  (-(s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2)) + (1 + s) * p3Rf σ s δ) / (2 * s * (1 - s))

lemma p3_costOne_eq (σ δ s : ℝ) :
    costOne σ δ s = if σ ^ 2 < s * δ then p3Ff σ s δ else 0 := rfl

lemma p3_yieldOne_eq (σ δ s : ℝ) :
    yieldOne σ δ s = if σ ^ 2 < s * δ then p3Gf σ s δ else 0 := rfl

lemma p3_sqrtQuad_convex (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ConvexOn ℝ Set.univ (fun x : ℝ => Real.sqrt (A * x ^ 2 + B)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hp0 : 0 ≤ Real.sqrt (A * x ^ 2 + B) := Real.sqrt_nonneg _
  have hq0 : 0 ≤ Real.sqrt (A * y ^ 2 + B) := Real.sqrt_nonneg _
  have hp : Real.sqrt (A * x ^ 2 + B) ^ 2 = A * x ^ 2 + B := Real.sq_sqrt (by positivity)
  have hq : Real.sqrt (A * y ^ 2 + B) ^ 2 = A * y ^ 2 + B := Real.sq_sqrt (by positivity)
  generalize Real.sqrt (A * x ^ 2 + B) = p at hp0 hp ⊢
  generalize Real.sqrt (A * y ^ 2 + B) = q at hq0 hq ⊢
  have hpq : A * x * y + B ≤ p * q := by
    have h1 : (A * x * y + B) ^ 2 ≤ (p * q) ^ 2 := by
      rw [mul_pow, hp, hq]; nlinarith [mul_nonneg (mul_nonneg hA hB) (sq_nonneg (x - y))]
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq (mul_nonneg hp0 hq0)] at h2
    exact (le_abs_self _).trans h2
  have hsum : 0 ≤ a * p + b * q := by positivity
  calc Real.sqrt (A * (a * x + b * y) ^ 2 + B) ≤ Real.sqrt ((a * p + b * q) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have hb' : b = 1 - a := by linarith
        subst hb'
        rw [show (a * p + (1 - a) * q) ^ 2 = a ^ 2 * p ^ 2 + (1 - a) ^ 2 * q ^ 2
          + 2 * (a * (1 - a)) * (p * q) by ring, hp, hq]
        nlinarith [mul_le_mul_of_nonneg_left hpq (mul_nonneg ha hb)]
    _ = a * p + b * q := Real.sqrt_sq hsum

lemma p3_conv_affine_add (R : ℝ → ℝ) (hR : ConvexOn ℝ Set.univ R) (k0 k1 k2 : ℝ)
    (hk2 : 0 ≤ k2) : ConvexOn ℝ Set.univ (fun δ => k1 * δ + k0 + k2 * R δ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := hR.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_le_mul_of_nonneg_left h hk2]

lemma p3_Rf_sq (σ s δ : ℝ) (hs0 : 0 < s) :
    p3Rf σ s δ ^ 2 = s ^ 2 * (1 - s) ^ 2 * δ ^ 2 + 4 * σ ^ 4 * s :=
  Real.sq_sqrt (by positivity)

lemma p3_Rf_nonneg (σ s δ : ℝ) : 0 ≤ p3Rf σ s δ := Real.sqrt_nonneg _

lemma p3_Rf_c (σ s : ℝ) (hs0 : 0 < s) : p3Rf σ s (σ ^ 2 / s) = σ ^ 2 * (1 + s) := by
  unfold p3Rf
  rw [show s ^ 2 * (1 - s) ^ 2 * (σ ^ 2 / s) ^ 2 + 4 * σ ^ 4 * s = (σ ^ 2 * (1 + s)) ^ 2 by
    field_simp; ring]
  exact Real.sqrt_sq (by positivity)

lemma p3_Ff_c (σ s : ℝ) (hs0 : 0 < s) : p3Ff σ s (σ ^ 2 / s) = 0 := by
  unfold p3Ff
  rw [p3_Rf_c σ s hs0]
  have : s * (1 - s) * (σ ^ 2 / s) = (1 - s) * σ ^ 2 := by field_simp
  rw [this]
  ring_nf

lemma p3_Gf_c (σ s : ℝ) (hs0 : 0 < s) : p3Gf σ s (σ ^ 2 / s) = 0 := by
  unfold p3Gf
  rw [p3_Rf_c σ s hs0]
  have : s * ((1 - s) ^ 2 * (σ ^ 2 / s) + 4 * σ ^ 2) = (1 - s) ^ 2 * σ ^ 2 + 4 * s * σ ^ 2 := by
    field_simp
  rw [this]
  ring_nf

lemma p3_Rf_mono (σ s x y : ℝ) (hx0 : 0 ≤ x) (hxy : x ≤ y) : p3Rf σ s x ≤ p3Rf σ s y := by
  unfold p3Rf
  apply Real.sqrt_le_sqrt
  have h2 : x ^ 2 ≤ y ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ s ^ 2 * (1 - s) ^ 2)
  linarith

lemma p3_Rf_le (σ s x : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hx0 : 0 ≤ x) (h : σ ^ 2 ≤ s * x) :
    p3Rf σ s x ≤ (1 + s) * s * x := by
  unfold p3Rf
  have hn : 0 ≤ (1 + s) * s * x := mul_nonneg (by positivity) hx0
  calc Real.sqrt (s ^ 2 * (1 - s) ^ 2 * x ^ 2 + 4 * σ ^ 4 * s)
      ≤ Real.sqrt (((1 + s) * s * x) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have h2 : σ ^ 4 ≤ (s * x) ^ 2 := by nlinarith [sq_nonneg σ]
        nlinarith [mul_le_mul_of_nonneg_left h2 hs0.le]
    _ = (1 + s) * s * x := Real.sqrt_sq hn

lemma p3_Rf_lt (σ s x : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1) (h : σ ^ 2 < s * x) :
    p3Rf σ s x < (1 + s) * s * x := by
  unfold p3Rf
  have hx0 : 0 < x := by
    by_contra hx; push Not at hx
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hs0.le hx, pow_pos hσ 2]
  have hn : 0 ≤ (1 + s) * s * x := by positivity
  calc Real.sqrt (s ^ 2 * (1 - s) ^ 2 * x ^ 2 + 4 * σ ^ 4 * s)
      < Real.sqrt (((1 + s) * s * x) ^ 2) := by
        apply Real.sqrt_lt_sqrt (by positivity)
        have h2 : σ ^ 4 < (s * x) ^ 2 := by
          have := mul_pos (sub_pos.2 h) (by positivity : (0:ℝ) < s * x + σ ^ 2)
          nlinarith
        nlinarith [mul_lt_mul_of_pos_left h2 hs0]
    _ = (1 + s) * s * x := Real.sqrt_sq hn

lemma p3_Ff_strict (σ s : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1) :
    StrictMonoOn (p3Ff σ s) (Set.Ici (σ ^ 2 / s)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have h1s : 0 < 1 - s := by linarith
  have hR := p3_Rf_mono σ s x y hx0 hxy.le
  have hl : s * (1 - s) * x < s * (1 - s) * y := mul_lt_mul_of_pos_left hxy (mul_pos hs0 h1s)
  unfold p3Ff
  apply (div_lt_div_iff_of_pos_right (by positivity)).2
  linarith

lemma p3_Gf_strict (σ s : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1) :
    StrictMonoOn (p3Gf σ s) (Set.Ici (σ ^ 2 / s)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have h1s : 0 < 1 - s := by linarith
  have hcx : σ ^ 2 ≤ s * x := by rw [div_le_iff₀ hs0] at hx; linarith
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have hcy : σ ^ 2 < s * y := by nlinarith
  have hpb := p3_Rf_le σ s x hs0 hs1 hx0 hcx
  have hqb := p3_Rf_lt σ s y hσ hs0 hs1 hcy
  have hp := p3_Rf_sq σ s x hs0
  have hq := p3_Rf_sq σ s y hs0
  have hp0 := p3_Rf_nonneg σ s x
  have hq0 := p3_Rf_nonneg σ s y
  have hσ4 : 0 < σ ^ 4 * s := mul_pos (pow_pos hσ 4) hs0
  unfold p3Gf
  generalize p3Rf σ s x = p at hpb hp hp0 ⊢
  generalize p3Rf σ s y = q at hqb hq hq0 ⊢
  have hqpos : 0 < q := by
    rcases lt_or_eq_of_le hq0 with h | h
    · exact h
    · rw [← h] at hq; nlinarith [sq_nonneg (s * (1 - s) * y)]
  have hk : 0 < s * (1 - s) ^ 2 * (y - x) := mul_pos (mul_pos hs0 (pow_pos h1s 2)) (sub_pos.2 hxy)
  have e : (q - p) * (p + q) = s ^ 2 * (1 - s) ^ 2 * (y ^ 2 - x ^ 2) := by
    linear_combination hq - hp
  have hsum : p + q < (1 + s) * s * (x + y) := by linarith
  have key : s * (1 - s) ^ 2 * (y - x) * (p + q) < (1 + s) * (q - p) * (p + q) := by
    have : (1 + s) * (q - p) * (p + q) = s * (1 - s) ^ 2 * (y - x) * ((1 + s) * s * (x + y)) := by
      rw [mul_assoc, e]; ring
    rw [this]; exact mul_lt_mul_of_pos_left hsum hk
  have hpq : 0 < p + q := by linarith
  have key2 : s * (1 - s) ^ 2 * (y - x) < (1 + s) * (q - p) := lt_of_mul_lt_mul_right key hpq.le
  apply (div_lt_div_iff_of_pos_right (by positivity)).2
  nlinarith [key2]

lemma p3_Ff_convex (σ s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : ConvexOn ℝ Set.univ (p3Ff σ s) := by
  have hR : ConvexOn ℝ Set.univ (p3Rf σ s) :=
    p3_sqrtQuad_convex (s ^ 2 * (1 - s) ^ 2) (4 * σ ^ 4 * s) (by positivity) (by positivity)
  have h1s : 0 < 1 - s := by linarith
  refine (p3_conv_affine_add (p3Rf σ s) hR (-(2 * σ ^ 2) / (2 * (1 - s)))
    (s * (1 - s) / (2 * (1 - s))) (1 / (2 * (1 - s))) (by positivity)).congr ?_
  intro δ _
  show _ = p3Ff σ s δ
  unfold p3Ff
  ring

lemma p3_Gf_convex (σ s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : ConvexOn ℝ Set.univ (p3Gf σ s) := by
  have hR : ConvexOn ℝ Set.univ (p3Rf σ s) :=
    p3_sqrtQuad_convex (s ^ 2 * (1 - s) ^ 2) (4 * σ ^ 4 * s) (by positivity) (by positivity)
  have h1s : 0 < 1 - s := by linarith
  refine (p3_conv_affine_add (p3Rf σ s) hR (-(s * (4 * σ ^ 2)) / (2 * s * (1 - s)))
    (-(s * (1 - s) ^ 2) / (2 * s * (1 - s))) ((1 + s) / (2 * s * (1 - s))) (by positivity)).congr ?_
  intro δ _
  show _ = p3Gf σ s δ
  unfold p3Gf
  ring

lemma p3_cost_max (σ s : ℝ) (hs0 : 0 < s) :
    ∀ δ, costOne σ δ s = p3Ff σ s (max δ (σ ^ 2 / s)) := by
  intro δ
  rw [p3_costOne_eq]
  split_ifs with h
  · rw [max_eq_left]; rw [div_le_iff₀ hs0]; linarith
  · push Not at h
    rw [max_eq_right (by rw [le_div_iff₀ hs0]; linarith), p3_Ff_c σ s hs0]

lemma p3_yield_max (σ s : ℝ) (hs0 : 0 < s) :
    ∀ δ, yieldOne σ δ s = p3Gf σ s (max δ (σ ^ 2 / s)) := by
  intro δ
  rw [p3_yieldOne_eq]
  split_ifs with h
  · rw [max_eq_left]; rw [div_le_iff₀ hs0]; linarith
  · push Not at h
    rw [max_eq_right (by rw [le_div_iff₀ hs0]; linarith), p3_Gf_c σ s hs0]

lemma p3_mono_of (c : ℝ) (H f : ℝ → ℝ) (hf : ∀ δ, f δ = H (max δ c))
    (hH : MonotoneOn H (Set.Ici c)) : MonotoneOn f (Set.Ici 0) := by
  intro x _ y _ hxy
  rw [hf, hf]
  exact hH (le_max_right x c) (le_max_right y c) (max_le_max hxy le_rfl)

lemma p3_strict_of (c : ℝ) (H f : ℝ → ℝ) (hf : ∀ δ, f δ = H (max δ c))
    (hH : StrictMonoOn H (Set.Ici c)) : StrictMonoOn f (Set.Ioi c) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  rw [hf, hf, max_eq_left hx.le, max_eq_left hy.le]
  exact hH (Set.mem_Ici.2 hx.le) (Set.mem_Ici.2 hy.le) hxy

lemma p3_conv_of (c : ℝ) (hc : 0 ≤ c) (H f : ℝ → ℝ) (hf : ∀ δ, f δ = H (max δ c))
    (hHc : ConvexOn ℝ Set.univ H) (hH : MonotoneOn H (Set.Ici c)) :
    ConvexOn ℝ (Set.Ici 0) f := by
  have himg : (fun δ : ℝ => max δ c) '' Set.Ici 0 = Set.Ici c := by
    ext y
    simp only [Set.mem_image, Set.mem_Ici]
    constructor
    · rintro ⟨x, -, rfl⟩; exact le_max_right _ _
    · intro hy; exact ⟨y, hc.trans hy, max_eq_left hy⟩
  have hmax : ConvexOn ℝ (Set.Ici 0) (fun δ : ℝ => max δ c) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left (le_max_left x c) ha,
        mul_le_mul_of_nonneg_left (le_max_left y c) hb]
    · nlinarith [mul_le_mul_of_nonneg_left (le_max_right x c) ha,
        mul_le_mul_of_nonneg_left (le_max_right y c) hb]
  have hcomp := ConvexOn.comp (g := H) (f := fun δ : ℝ => max δ c) (s := Set.Ici 0)
    (by rw [himg]; exact hHc.subset (Set.subset_univ _) (convex_Ici c)) hmax
    (by rw [himg]; exact hH)
  exact hcomp.congr (fun δ _ => (hf δ).symm)

lemma p3_Gf_root (σ s δ : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    p3Gf σ s δ * (σ ^ 2 * (1 + s) ^ 2) =
      (1 - s) * (s * δ - p3Gf σ s δ - σ ^ 2) * ((δ + p3Gf σ s δ) * s - σ ^ 2) := by
  have h1s : 0 < 1 - s := by linarith
  have hR2 := p3_Rf_sq σ s δ hs0
  have hD0 : 2 * s * (1 - s) ≠ 0 := by positivity
  have hG : 2 * s * (1 - s) * p3Gf σ s δ =
      -(s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2)) + (1 + s) * p3Rf σ s δ := by
    unfold p3Gf; field_simp
  have hN : (-(s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2)) + (1 + s) * p3Rf σ s δ) ^ 2
      + 2 * (s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2))
        * (-(s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2)) + (1 + s) * p3Rf σ s δ)
      - 4 * s * (1 - s) ^ 2 * (s * δ - σ ^ 2) ^ 2 = 0 := by
    linear_combination (1 + s) ^ 2 * hR2
  generalize p3Gf σ s δ = G at hG ⊢
  generalize p3Rf σ s δ = R at hG hN
  have h4 : 4 * s * (1 - s) ≠ 0 := by positivity
  apply mul_left_cancel₀ h4
  linear_combination hN + (-(s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2)) + (1 + s) * R
    + 2 * s * (1 - s) * G + 2 * (s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2))) * hG

lemma p3_Ff_of_Gf (σ s δ : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ((δ + p3Gf σ s δ) * s - σ ^ 2) / (1 + s) = p3Ff σ s δ := by
  have h1s : 0 < 1 - s := by linarith
  have h1s' : (1 - s) ≠ 0 := h1s.ne'
  unfold p3Gf p3Ff
  field_simp
  ring

lemma p3_Gf_lin (σ s δ : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (1 - s) * s * p3Gf σ s δ + s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2) =
      ((1 + s) * p3Rf σ s δ + s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2)) / 2 := by
  have h1s : 0 < 1 - s := by linarith
  have h1s' : (1 - s) ≠ 0 := h1s.ne'
  unfold p3Gf
  field_simp
  ring

lemma p3_equiv (σ s : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ δ Φ Γ : ℝ, 0 ≤ δ → 0 ≤ Γ →
      (IsOneAssetSystem σ δ s Φ Γ ↔ Φ = costOne σ δ s ∧ Γ = yieldOne σ δ s) := by
  intro δ Φ Γ hδ hΓ
  rw [p3_costOne_eq, p3_yieldOne_eq]
  unfold IsOneAssetSystem
  by_cases h : σ ^ 2 < s * δ
  · simp only [if_pos h]
    have h1s : 0 < 1 - s := by linarith
    have hroot := p3_Gf_root σ s δ hs0 hs1
    have hphi := p3_Ff_of_Gf σ s δ hs0 hs1
    have hlin := p3_Gf_lin σ s δ hs0 hs1
    have hD : σ ^ 2 * (1 + s) ^ 2 ≠ 0 := by positivity
    have hB : 0 < s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2) :=
      mul_pos hs0 (by nlinarith [mul_nonneg (sq_nonneg (1 - s)) hδ, pow_pos hσ 2])
    have hR0 := p3_Rf_nonneg σ s δ
    constructor
    · rintro ⟨h1, h2⟩
      rw [eq_div_iff hD] at h2
      have hfac : (Γ - p3Gf σ s δ) *
          ((1 - s) * s * (Γ + p3Gf σ s δ) + s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2)) = 0 := by
        linear_combination h2 - hroot
      have hpos : 0 < (1 - s) * s * (Γ + p3Gf σ s δ) + s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2) := by
        have e1 : 0 ≤ (1 - s) * s * Γ := mul_nonneg (mul_nonneg h1s.le hs0.le) hΓ
        have e2 : 0 ≤ (1 + s) * p3Rf σ s δ := mul_nonneg (by linarith) hR0
        nlinarith [hlin]
      have hΓeq : Γ = p3Gf σ s δ := by
        rcases mul_eq_zero.1 hfac with h3 | h3
        · linarith
        · linarith
      refine ⟨?_, hΓeq⟩
      rw [h1, hΓeq, hphi]
    · rintro ⟨h1, h2⟩
      subst h2
      refine ⟨by rw [h1, hphi], ?_⟩
      rw [eq_div_iff hD]
      exact hroot
  · simp only [if_neg h]

end CostlyShort.OneAsset

open CostlyShort.OneAsset in
theorem solution (σ s : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1) :
    (∀ δ Φ Γ : ℝ, 0 ≤ δ → 0 ≤ Γ →
      (IsOneAssetSystem σ δ s Φ Γ ↔ Φ = costOne σ δ s ∧ Γ = yieldOne σ δ s)) ∧
    MonotoneOn (fun δ => costOne σ δ s) (Set.Ici 0) ∧
    StrictMonoOn (fun δ => costOne σ δ s) (Set.Ioi (σ ^ 2 / s)) ∧
    ConvexOn ℝ (Set.Ici 0) (fun δ => costOne σ δ s) ∧
    MonotoneOn (fun δ => yieldOne σ δ s) (Set.Ici 0) ∧
    StrictMonoOn (fun δ => yieldOne σ δ s) (Set.Ioi (σ ^ 2 / s)) ∧
    ConvexOn ℝ (Set.Ici 0) (fun δ => yieldOne σ δ s) := by
  have hc : 0 ≤ σ ^ 2 / s := by positivity
  have hcF := p3_cost_max σ s hs0
  have hcG := p3_yield_max σ s hs0
  have hFs := p3_Ff_strict σ s hσ hs0 hs1
  have hGs := p3_Gf_strict σ s hσ hs0 hs1
  have hFc := p3_Ff_convex σ s hs0 hs1
  have hGc := p3_Gf_convex σ s hs0 hs1
  exact ⟨p3_equiv σ s hσ hs0 hs1,
    p3_mono_of _ _ (fun δ => costOne σ δ s) hcF hFs.monotoneOn,
    p3_strict_of _ _ (fun δ => costOne σ δ s) hcF hFs,
    p3_conv_of _ hc _ (fun δ => costOne σ δ s) hcF hFc hFs.monotoneOn,
    p3_mono_of _ _ (fun δ => yieldOne σ δ s) hcG hGs.monotoneOn,
    p3_strict_of _ _ (fun δ => yieldOne σ δ s) hcG hGs,
    p3_conv_of _ hc _ (fun δ => yieldOne σ δ s) hcG hGc hGs.monotoneOn⟩
