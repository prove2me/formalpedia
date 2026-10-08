-- Prove2me | solution 1 for DimCallCenters.Rationalized.eq_13_14
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T03:59:31.179448+00:00
-- url     : https://prove2.me/submissions/c4e9ad90-1f3c-45a7-83ac-d3e857d08d09

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Flam

open Filter Topology

open DimCallCenters.Rationalized in
lemma flam_ratio_key_16f466fc (μ : ℝ) (hμ : 0 < μ) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (lam : ℝ) (hlam : 0 < lam) (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) :
    a / b ≤ Flam F μ lam a / Flam F μ lam b := by
  have hc : 0 < lam / μ := div_pos hlam hμ
  have hs : 0 < Real.sqrt (lam / μ) := Real.sqrt_pos.2 hc
  have ha : 0 < a := lt_of_lt_of_le hb hba
  unfold Flam servers
  set c0 := lam / μ with hc0
  set s := Real.sqrt (lam / μ) with hs0
  have hz : c0 ∈ Set.Ioi (0:ℝ) := hc
  have hy : c0 + a * s ∈ Set.Ioi (0:ℝ) := by
    show 0 < c0 + a * s; positivity
  have hx : c0 + b * s ∈ Set.Ioi (0:ℝ) := by
    show 0 < c0 + b * s; positivity
  have hw1 : (0:ℝ) ≤ b / a := div_nonneg hb.le ha.le
  have hw2 : (0:ℝ) ≤ 1 - b / a := sub_nonneg.2 ((div_le_one ha).2 hba)
  have hconv := hFconv.2 hy hz hw1 hw2 (by ring)
  have heq : (b / a) • (c0 + a * s) + (1 - b / a) • c0 = c0 + b * s := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [heq] at hconv
  simp only [smul_eq_mul] at hconv
  have hpos : 0 < F (c0 + b * s) - F c0 := by
    have : c0 < c0 + b * s := by have := mul_pos hb hs; linarith
    exact sub_pos.2 (hFmono hz hx this)
  rw [div_le_div_iff₀ hb hpos]
  have h2 := mul_le_mul_of_nonneg_left hconv ha.le
  have h3 : a * (b / a * F (c0 + a * s) + (1 - b / a) * F c0)
      = b * F (c0 + a * s) + (a - b) * F c0 := by
    field_simp
  rw [h3] at h2
  nlinarith

open DimCallCenters.Rationalized in
lemma flam_ratio_ge_16f466fc (μ : ℝ) (hμ : 0 < μ) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (lam : ℝ) (hlam : 0 < lam) (a b : ℝ) (hb : 0 < b) (c : ℝ) (hc : 1 ≤ c)
    (hle : c ≤ a / b) : c ≤ Flam F μ lam a / Flam F μ lam b := by
  have hba : b ≤ a := by
    have : 1 ≤ a / b := hc.trans hle
    rwa [le_div_iff₀ hb, one_mul] at this
  exact hle.trans (flam_ratio_key_16f466fc μ hμ F hFconv hFmono lam hlam a b hb hba)

open Filter Topology DimCallCenters.Rationalized in
theorem solution (μ : ℝ) (hμ : 0 < μ) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (a b : ℝ → ℝ) (ha : ∀ lam : ℝ, 0 < lam → 0 < a lam) (hb : ∀ lam : ℝ, 0 < lam → 0 < b lam) :
    ((∃ c : ℝ, 1 < c ∧ ∃ᶠ lam in atTop, c ≤ a lam / b lam) →
      ∃ c : ℝ, 1 < c ∧ ∃ᶠ lam in atTop, c ≤ Flam F μ lam (a lam) / Flam F μ lam (b lam)) ∧
    ((∀ C : ℝ, ∃ᶠ lam in atTop, C ≤ a lam / b lam) →
      ∀ C : ℝ, ∃ᶠ lam in atTop, C ≤ Flam F μ lam (a lam) / Flam F μ lam (b lam)) := by
  have hev : ∀ᶠ lam in atTop, (0:ℝ) < lam := eventually_gt_atTop 0
  refine ⟨fun ⟨c, hc1, hfr⟩ => ⟨c, hc1, ?_⟩, fun h C => ?_⟩
  · refine (hfr.and_eventually hev).mono ?_
    rintro lam ⟨hle, hlam⟩
    exact flam_ratio_ge_16f466fc μ hμ F hFconv hFmono lam hlam (a lam) (b lam) (hb lam hlam)
      c hc1.le hle
  · refine ((h (max C 1)).and_eventually hev).mono ?_
    rintro lam ⟨hle, hlam⟩
    exact (le_max_left C 1).trans (flam_ratio_ge_16f466fc μ hμ F hFconv hFmono lam hlam (a lam)
      (b lam) (hb lam hlam) (max C 1) (le_max_right C 1) hle)
