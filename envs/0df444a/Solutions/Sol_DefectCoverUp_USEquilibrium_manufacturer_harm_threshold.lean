-- Prove2me | solution 1 for DefectCoverUp.USEquilibrium.manufacturer_harm_threshold
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:14:27.807555+00:00
-- url     : https://prove2.me/submissions/3dbb13ad-39c2-4d4a-ada3-144e4bf5aadd

import Mathlib
import Definitions.Def_DefectCoverUp_USEquilibrium_Model

open DefectCoverUp.USEquilibrium

/-- A cubic with negative leading coefficient, negative at `0` and positive at `H > 0`,
changes sign exactly once on `[0, H]`. -/
lemma cu_cubic_threshold (f : ℝ → ℝ) (a b c e H : ℝ) (ha : a < 0)
    (hf : ∀ x, f x = a * x ^ 3 + b * x ^ 2 + c * x + e) (hH : 0 < H)
    (h0 : f 0 < 0) (h1 : 0 < f H) :
    ∃ s ∈ Set.Ioo 0 H, ∀ x ∈ Set.Icc (0 : ℝ) H, (0 ≤ f x ↔ s ≤ x) := by
  have hcont : ContinuousOn f (Set.Icc 0 H) := by
    have : f = fun x => a * x ^ 3 + b * x ^ 2 + c * x + e := funext hf
    rw [this]; fun_prop
  obtain ⟨s, ⟨hs0, hsH⟩, hs⟩ :=
    intermediate_value_Ioo hH.le hcont (show (0 : ℝ) ∈ Set.Ioo (f 0) (f H) from ⟨h0, h1⟩)
  set q : ℝ → ℝ := fun x => a * x ^ 2 + (b + a * s) * x + (c + b * s + a * s ^ 2) with hq
  have hfs : a * s ^ 3 + b * s ^ 2 + c * s + e = 0 := by rw [← hf]; exact hs
  have hfac : ∀ x, f x = (x - s) * q x := by
    intro x; rw [hf]; simp only [hq]; linear_combination hfs
  have hq0 : 0 < q 0 := by
    have := hfac 0; rw [this] at h0; nlinarith
  have hqH : 0 < q H := by
    have := hfac H; rw [this] at h1
    by_contra hc; have hc := not_lt.mp hc; nlinarith
  have hqpos : ∀ x ∈ Set.Icc (0 : ℝ) H, 0 < q x := by
    rintro x ⟨hx0, hxH⟩
    have key : H * q x = (H - x) * q 0 + x * q H - a * x * (H - x) * H := by
      simp only [hq]; ring
    have : 0 < H * q x := by
      rw [key]
      have h2 : 0 ≤ -a * x * (H - x) * H := by
        have : 0 ≤ -a := by linarith
        have : 0 ≤ H - x := by linarith
        positivity
      rcases eq_or_lt_of_le hx0 with hx | hx
      · subst hx; nlinarith
      · nlinarith [mul_pos hx hqH, mul_nonneg (sub_nonneg.mpr hxH) hq0.le]
    exact pos_of_mul_pos_right this hH.le
  refine ⟨s, ⟨hs0, hsH⟩, fun x hx => ?_⟩
  have hqx := hqpos x hx
  rw [hfac x]
  constructor
  · intro h; by_contra hc; have hc := not_le.mp hc
    have : (x - s) * q x < 0 := mul_neg_of_neg_of_pos (by linarith) hqx
    linarith
  · intro h; exact mul_nonneg (by linarith) hqx.le

theorem solution (P : Params) (hP : P.Standing) :
    (∃ a b c : ℝ, ∀ h : ℝ,
      Omega1hat P h = -P.l / (P.hbar * P.vbar) * h ^ 3 +
        a * h ^ 2 + b * h + c) ∧
    -P.l / (P.hbar * P.vbar) < 0 ∧
    Omega1hat P 0 = -P.l * P.r * (1 - P.p / P.vbar) ∧
    Omega1hat P 0 < 0 ∧
    Omega1hat P P.hbar =
      (1 / (2 * P.vbar)) *
        ((1 - P.l) * (P.vbar - P.p) * P.r + 2 * P.K2 * P.th * P.vbar +
          P.hbar * ((1 - P.l) * (P.vbar - P.p) + 2 * P.K1 * P.th * P.vbar)) ∧
    0 < Omega1hat P P.hbar ∧
    ∃ hR ∈ Set.Ioo 0 P.hbar,
      ∀ h ∈ Set.Icc (0 : ℝ) P.hbar, (0 ≤ Omega1hat P h ↔ hR ≤ h) := by
  obtain ⟨hp, hr, hrp, hH, hpv, hC, hl0, hl1, hth0, hth1, hal0, hal1, hK1, hK2, hPD0, hPD1⟩ := hP
  have hv : 0 < P.vbar := by linarith
  set A : ℝ := P.K1 * P.th / P.hbar +
      (1 - 2 * P.al + P.l) * (1 - P.p / P.vbar) / (2 * P.hbar) +
      P.l / P.vbar + P.l * (P.p - P.r) / (P.hbar * P.vbar) with hA
  set B : ℝ := P.K2 * P.th / P.hbar +
      (2 * P.al * P.hbar + (1 + P.l) * P.r) * (1 - P.p / P.vbar) / (2 * P.hbar) +
      P.l * P.r / P.vbar - P.l * (1 - P.p / P.vbar) - P.p * P.l / P.vbar with hB
  have hform : ∀ h : ℝ, Omega1hat P h = -P.l / (P.hbar * P.vbar) * h ^ 3 +
      A * h ^ 2 + B * h + (-P.l * P.r * (1 - P.p / P.vbar)) := by
    intro h; unfold Omega1hat Omega1; rw [hA, hB]; ring
  have hlead : -P.l / (P.hbar * P.vbar) < 0 := by
    rw [neg_div]; exact neg_neg_of_pos (by positivity)
  have hz : Omega1hat P 0 = -P.l * P.r * (1 - P.p / P.vbar) := by rw [hform]; ring
  have hzneg : Omega1hat P 0 < 0 := by
    rw [hz]
    have : 0 < 1 - P.p / P.vbar := by
      rw [sub_pos, div_lt_one hv]; linarith
    have := mul_pos (mul_pos hl0 hr) this
    linarith
  have hHv : Omega1hat P P.hbar =
      (1 / (2 * P.vbar)) *
        ((1 - P.l) * (P.vbar - P.p) * P.r + 2 * P.K2 * P.th * P.vbar +
          P.hbar * ((1 - P.l) * (P.vbar - P.p) + 2 * P.K1 * P.th * P.vbar)) := by
    rw [hform, hA, hB]; field_simp; ring
  have hHpos : 0 < Omega1hat P P.hbar := by
    rw [hHv]
    have h1 : 0 < (1 - P.l) * (P.vbar - P.p) * P.r := by
      have : 0 < 1 - P.l := by linarith
      have : 0 < P.vbar - P.p := by linarith
      positivity
    have h2 : 0 ≤ 2 * P.K2 * P.th * P.vbar := by positivity
    have h3 : 0 ≤ P.hbar * ((1 - P.l) * (P.vbar - P.p) + 2 * P.K1 * P.th * P.vbar) := by
      have : 0 < 1 - P.l := by linarith
      have : 0 < P.vbar - P.p := by linarith
      positivity
    positivity
  refine ⟨⟨A, B, _, hform⟩, hlead, hz, hzneg, hHv, hHpos, ?_⟩
  exact cu_cubic_threshold (Omega1hat P) _ _ _ _ _ hlead hform hH hzneg hHpos
