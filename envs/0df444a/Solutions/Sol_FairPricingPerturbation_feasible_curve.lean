-- Prove2me | solution 1 for FairPricingPerturbation.feasible_curve
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:31.20344+00:00
-- url     : https://prove2.me/submissions/61fc7b70-3822-443e-8c5e-745af2325eaf

import Mathlib

namespace CohenPriceFairness.LocalWelfare.Sol_core_feasible_curve

open Filter Topology Asymptotics Set

theorem c1_deriv_est {f : ℝ → ℝ} {m a : ℝ} (hf : HasDerivAt f m a) {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ > 0, ∀ X, |X| < δ → |f (a + X) - f a - X * m| ≤ κ * |X| := by
  have h := (hasDerivAt_iff_isLittleO_nhds_zero.mp hf).def hκ
  rcases Metric.eventually_nhds_iff.mp h with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, fun X hX => ?_⟩
  have := hball (y := X) (by simpa [Real.dist_eq] using hX)
  simpa [Real.norm_eq_abs, smul_eq_mul] using this

theorem c1_core (f g : ℝ → ℝ) (a c m n u w : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hcont : ∃ η > 0, ContinuousOn f (Icc (a - η) (a + η)))
    (hf : HasDerivAt f m a) (hg : HasDerivAt g n c) (hm : m ≠ 0)
    (hv : m * u + n * w = -(f a + g c)) :
    ∀ τ > 0, ∃ ε > 0, ∀ α ∈ Ioc (0 : ℝ) ε, ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧
      |f x + g y| ≤ (1 - α) * |f a + g c| ∧ |x - a - α * u| ≤ τ * α ∧
      |y - c - α * w| ≤ τ * α := by
  intro τ hτ
  obtain ⟨η, hη, hfc⟩ := hcont
  set L := |u| + |w| + τ + 1 with hL
  have hLpos : 0 < L := by positivity
  have hm' : 0 < |m| := abs_pos.mpr hm
  set κ := |m| * τ / (2 * L) with hκdef
  have hκ : 0 < κ := by positivity
  obtain ⟨δ1, hδ1, e1⟩ := c1_deriv_est hf hκ
  obtain ⟨δ2, hδ2, e2⟩ := c1_deriv_est hg hκ
  refine ⟨min 1 (min (δ1 / (2 * L)) (min (δ2 / (2 * L)) (min (η / L) (min (a / L) (c / L))))),
    by positivity, ?_⟩
  rintro α ⟨hα0, hαε⟩
  simp only [le_min_iff] at hαε
  obtain ⟨hα1, hαd1, hαd2, hαη, hαa, hαc⟩ := hαε
  rw [le_div_iff₀ (by positivity)] at hαd1 hαd2
  rw [le_div_iff₀ hLpos] at hαη hαa hαc
  have hu : |u| ≤ L := by rw [hL]; linarith [abs_nonneg w]
  have hw : |w| ≤ L := by rw [hL]; linarith [abs_nonneg u]
  have hut : |u| + τ ≤ L := by rw [hL]; linarith [abs_nonneg w]
  have hαut := mul_le_mul_of_nonneg_left hut hα0.le
  have hαw := mul_le_mul_of_nonneg_left hw hα0.le
  set s := τ * α with hs
  have hs0 : 0 < s := by positivity
  set Δ := f a + g c with hΔ
  let h : ℝ → ℝ := fun t => f (a + α * u + t) + g (c + α * w) - (1 - α) * Δ
  -- key expansion
  have hY : |α * w| < δ2 := by
    rw [abs_mul, abs_of_pos hα0]
    nlinarith [mul_le_mul_of_nonneg_left hw hα0.le]
  have E2 := e2 (α * w) hY
  have key : ∀ t, |t| ≤ s → |h t - m * t| ≤ κ * α * (|u| + τ + |w|) := by
    intro t ht
    have hX : |α * u + t| < δ1 := by
      calc |α * u + t| ≤ |α * u| + |t| := abs_add_le _ _
        _ ≤ α * L := by
          rw [abs_mul, abs_of_pos hα0]
          nlinarith [mul_le_mul_of_nonneg_left hut hα0.le]
        _ < δ1 := by nlinarith
    have E1 := e1 (α * u + t) hX
    have : h t - m * t = (f (a + (α * u + t)) - f a - (α * u + t) * m)
        + (g (c + α * w) - g c - α * w * n) := by
      simp only [h, ← add_assoc]
      have : α * Δ = - (α * (m * u + n * w)) := by rw [hv]; ring
      linear_combination this
    rw [this]
    have hXb : |α * u + t| ≤ α * |u| + α * τ := by
      calc |α * u + t| ≤ |α * u| + |t| := abs_add_le _ _
        _ ≤ α * |u| + α * τ := by rw [abs_mul, abs_of_pos hα0]; linarith
    have hYb : |α * w| = α * |w| := by rw [abs_mul, abs_of_pos hα0]
    calc _ ≤ |f (a + (α * u + t)) - f a - (α * u + t) * m| + |g (c + α * w) - g c - α * w * n| :=
          abs_add_le _ _
      _ ≤ κ * |α * u + t| + κ * |α * w| := add_le_add E1 E2
      _ ≤ κ * (α * |u| + α * τ) + κ * (α * |w|) := by
          rw [hYb]; gcongr
      _ = κ * α * (|u| + τ + |w|) := by ring
  have hbound : κ * α * (|u| + τ + |w|) < |m| * s := by
    have h1 : κ * (|u| + τ + |w|) < |m| * τ := by
      rw [hκdef]
      have : |u| + τ + |w| < 2 * L := by rw [hL]; linarith [abs_nonneg u, abs_nonneg w]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos hm' hτ]
    rw [hs]; nlinarith
  -- continuity of h on [-s, s]
  have hcont_h : ContinuousOn h (uIcc (-s) s) := by
    rw [uIcc_of_le (by linarith)]
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.add _ continuousOn_const
    apply hfc.comp (by fun_prop)
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hau := neg_abs_le u
    have hau' := le_abs_self u
    have h1 := mul_le_mul_of_nonneg_left hau hα0.le
    have h2 := mul_le_mul_of_nonneg_left hau' hα0.le
    constructor <;> nlinarith
  have hsign : (0 : ℝ) ∈ uIcc (h (-s)) (h s) := by
    have k1 := abs_le.mp (le_trans (key s (by rw [abs_of_pos hs0])) hbound.le)
    have k2 := abs_le.mp (le_trans (key (-s) (by rw [abs_neg, abs_of_pos hs0])) hbound.le)
    rw [mul_neg] at k2
    obtain ⟨k1a, k1b⟩ := k1
    obtain ⟨k2a, k2b⟩ := k2
    rw [mem_uIcc]
    rcases lt_or_gt_of_ne hm with hneg | hpos
    · rw [abs_of_neg hneg] at hbound k1a k1b k2a k2b
      right
      constructor <;> linarith
    · rw [abs_of_pos hpos] at hbound k1a k1b k2a k2b
      left
      constructor <;> linarith
  obtain ⟨t, ht, hht⟩ := intermediate_value_uIcc hcont_h hsign
  rw [uIcc_of_le (by linarith)] at ht
  obtain ⟨ht1, ht2⟩ := ht
  refine ⟨a + α * u + t, c + α * w, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left (neg_abs_le u) hα0.le
    have h3 : α * L ≤ a := hαa
    have h4 : α * (|u| + τ) = α * |u| + τ * α := by ring
    have h5 : α * -|u| = -(α * |u|) := by ring
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (neg_abs_le w) hα0.le
    have h5 : α * -|w| = -(α * |w|) := by ring
    have h6 : α * |w| ≤ α * L := hαw
    linarith
  · have : f (a + α * u + t) + g (c + α * w) = (1 - α) * Δ := by
      simp only [h] at hht; linarith
    rw [this, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - α)]
  · rw [show a + α * u + t - a - α * u = t by ring, abs_le]; constructor <;> linarith
  · rw [show c + α * w - c - α * w = 0 by ring, abs_zero]; positivity

end CohenPriceFairness.LocalWelfare.Sol_core_feasible_curve

open CohenPriceFairness.LocalWelfare CohenPriceFairness.LocalWelfare.Sol_core_feasible_curve
open Filter Topology Asymptotics Set

theorem solution
    (M : Fin 2 → ℝ → ℝ) (b mm v : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hMd : ∀ i, HasDerivAt (M i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hv : mm 0 * v 0 - mm 1 * v 1 = -(M 0 (b 0) - M 1 (b 1))) :
    ∀ τ > 0, ∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε, ∃ q : Fin 2 → ℝ,
      (∀ i, 0 ≤ q i) ∧
      |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)| ∧
      ∀ i, |q i - b i - α * v i| ≤ τ * α := by
  intro τ hτ
  obtain ⟨η, hη, hc⟩ := hcont
  rcases hmm with h0 | h1
  · obtain ⟨ε, hε, H⟩ := c1_core (M 0) (fun y => -M 1 y) (b 0) (b 1) (mm 0) (-mm 1) (v 0) (v 1)
      (hb 0) (hb 1) ⟨η, hη, hc 0⟩ (hMd 0) (hMd 1).neg h0 (by linear_combination hv) τ hτ
    refine ⟨ε, hε, fun α hα => ?_⟩
    obtain ⟨x, y, hx, hy, hD, hxv, hyv⟩ := H α hα
    refine ⟨![x, y], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simpa
    · simpa [sub_eq_add_neg] using hD
    · intro i; fin_cases i <;> simpa
  · obtain ⟨ε, hε, H⟩ := c1_core (fun y => -M 1 y) (M 0) (b 1) (b 0) (-mm 1) (mm 0) (v 1) (v 0)
      (hb 1) (hb 0) ⟨η, hη, (hc 1).neg⟩ (hMd 1).neg (hMd 0) (neg_ne_zero.mpr h1)
      (by linear_combination hv) τ hτ
    refine ⟨ε, hε, fun α hα => ?_⟩
    obtain ⟨x, y, hx, hy, hD, hxv, hyv⟩ := H α hα
    refine ⟨![y, x], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simpa
    · have e1 : M 0 y - M 1 x = -M 1 x + M 0 y := by ring
      have e2 : M 0 (b 0) - M 1 (b 1) = -M 1 (b 1) + M 0 (b 0) := by ring
      simpa [e1, e2] using hD
    · intro i; fin_cases i <;> simpa
