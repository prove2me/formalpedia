-- Prove2me | solution 1 for DimCallCenters.QualityDriven.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:11:31.00432+00:00
-- url     : https://prove2.me/submissions/eb5ffe0e-c7de-4230-b638-52c1d38cd24d

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Clam
import Definitions.Def_DimCallCenters_Rationalized_surrogate

open Filter Topology

theorem p2m025366fb_ratio_bound (a b A B : ℝ) (hab : a ≤ b) (hBA : B ≤ A)
    (hv : 0 < a / A) (hu : 0 < b / B) :
    |b / a - 1| ≤ |(b / B) / (a / A) - 1| := by
  have ha : a ≠ 0 := by rintro rfl; simp at hv
  have hA : A ≠ 0 := by rintro rfl; simp at hv
  have hb : b ≠ 0 := by rintro rfl; simp at hu
  have hB : B ≠ 0 := by rintro rfl; simp at hu
  have heq : (b / B) / (a / A) = (b / a) * (A / B) := by
    field_simp
  rw [heq]
  rcases lt_or_gt_of_ne ha with ha' | ha'
  · -- a < 0, so A < 0
    have hA' : A < 0 := by
      by_contra h; rw [not_lt] at h
      have : a / A ≤ 0 := div_nonpos_of_nonpos_of_nonneg ha'.le h
      linarith
    have hb' : b < 0 := by
      rcases lt_or_gt_of_ne hb with h | h
      · exact h
      · exfalso
        have hB' : 0 < B := by
          by_contra h2; rw [not_lt] at h2
          have : b / B ≤ 0 := div_nonpos_of_nonneg_of_nonpos h.le h2
          linarith
        linarith
    have hB' : B < 0 := by linarith
    have h1 : b / a ≤ 1 := by rw [div_le_one_of_neg ha']; exact hab
    have h0 : 0 < b / a := div_pos_of_neg_of_neg hb' ha'
    have h2 : A / B ≤ 1 := by rw [div_le_one_of_neg hB']; exact hBA
    have h3 : 0 < A / B := div_pos_of_neg_of_neg hA' hB'
    have h4 : b / a * (A / B) ≤ b / a := by nlinarith
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by nlinarith)]
    linarith
  · -- 0 < a, so 0 < A
    have hA' : 0 < A := by
      by_contra h; rw [not_lt] at h
      have : a / A ≤ 0 := div_nonpos_of_nonneg_of_nonpos ha'.le h
      linarith
    have hb' : 0 < b := by linarith
    have hB' : 0 < B := by
      by_contra h2; rw [not_lt] at h2
      have : b / B ≤ 0 := div_nonpos_of_nonneg_of_nonpos hb'.le h2
      linarith
    have h1 : 1 ≤ b / a := by rw [one_le_div ha']; exact hab
    have h2 : 1 ≤ A / B := by rw [one_le_div hB']; exact hBA
    have h4 : b / a ≤ b / a * (A / B) := by nlinarith
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by nlinarith)]
    linarith

open Filter Topology in
theorem solution (M : DimCallCenters.Rationalized.WaitModel) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (Fh pih Gh : ℝ → ℝ → ℝ) (x z : ℝ → ℝ)
    (hx : ∀ lam : ℝ, 0 < lam → 0 < x lam ∧
      ∀ x' : ℝ, 0 < x' → DimCallCenters.Rationalized.Clam M F lam (x lam) ≤ DimCallCenters.Rationalized.Clam M F lam x')
    (hz : ∀ lam : ℝ, 0 < lam → 0 < z lam ∧
      ∀ z' : ℝ, 0 < z' →
        DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (z lam) ≤ DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) z')
    (hxapprox : Tendsto (fun lam => DimCallCenters.Rationalized.Clam M F lam (x lam) /
      DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (x lam)) atTop (𝓝 1))
    (hzapprox : Tendsto (fun lam => DimCallCenters.Rationalized.Clam M F lam (z lam) /
      DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (z lam)) atTop (𝓝 1)) :
    Tendsto (fun lam => DimCallCenters.Rationalized.Clam M F lam (z lam) / DimCallCenters.Rationalized.Clam M F lam (x lam)) atTop (𝓝 1) := by
  have ht := hzapprox.div hxapprox one_ne_zero
  rw [div_one] at ht
  have ht0 : Tendsto (fun lam =>
      (DimCallCenters.Rationalized.Clam M F lam (z lam) /
        DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (z lam)) /
      (DimCallCenters.Rationalized.Clam M F lam (x lam) /
        DimCallCenters.Rationalized.surrogate (Fh lam) (pih lam) (Gh lam) (x lam)) - 1)
      atTop (𝓝 0) := by
    have := ht.sub_const 1
    simpa using this
  have hu := hzapprox.eventually (lt_mem_nhds (show (0:ℝ) < 1 by norm_num))
  have hv := hxapprox.eventually (lt_mem_nhds (show (0:ℝ) < 1 by norm_num))
  have hpos : ∀ᶠ lam : ℝ in atTop, 0 < lam := eventually_gt_atTop 0
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ (by simpa using ht0.norm)
  filter_upwards [hu, hv, hpos] with lam hu hv hl
  exact p2m025366fb_ratio_bound _ _ _ _ ((hx lam hl).2 _ (hz lam hl).1)
    ((hz lam hl).2 _ (hx lam hl).1) hv hu
