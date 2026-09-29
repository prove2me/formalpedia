-- Prove2me | solution 1 for CachonPushPull.ShippingCost.retailer_prebook_argmax
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:26:03.881382+00:00
-- url     : https://prove2.me/submissions/f684f9fc-6cc9-43de-b04d-3298d9cfebd0

import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory

/-- Under the demand model, the cdf vanishes on `(-∞, 0]`. -/
theorem aux_rpa_cdf_nonpos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (x : ℝ) (hx : x ≤ 0) : cdf μ x = 0 :=
  le_antisymm (hD.cdf_zero ▸ monotone_cdf μ hx) (cdf_nonneg μ x)

/-- Under the demand model, the cdf is continuous. -/
theorem aux_rpa_cdf_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) : Continuous (fun x => cdf μ x) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x 0 with h | h | h
  · have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds x] fun y => cdf μ y := by
      filter_upwards [Iio_mem_nhds h] with y hy
      exact (aux_rpa_cdf_nonpos μ f hD y (le_of_lt hy)).symm
    exact continuousAt_const.congr hev
  · subst h
    rw [continuousAt_iff_continuous_left_right]
    constructor
    · have h0 : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Set.Iic 0) 0 :=
        continuousWithinAt_const
      exact h0.congr (fun y hy => aux_rpa_cdf_nonpos μ f hD y hy)
        (aux_rpa_cdf_nonpos μ f hD 0 le_rfl)
    · exact (cdf μ).right_continuous 0
  · exact (hD.hasDerivAt x h).continuousAt

end CachonPushPull.ShippingCost

open CachonPushPull.ShippingCost
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (w₁ w₂ : ℝ) (hvw₁ : v < w₁) (hw₁₂ : w₁ ≤ w₂) (hw₂p : w₂ ≤ p) (q : ℝ) :
    ConcaveOn ℝ (Set.Ici 0) (fun y : ℝ => retailerProfit μ p v w₁ w₂ y q) ∧
    (∃ yr : ℝ, 0 ≤ yr ∧ cdf μ yr = (w₂ - w₁) / (w₂ - v)) ∧
    ∀ yr : ℝ, 0 ≤ yr → cdf μ yr = (w₂ - w₁) / (w₂ - v) →
      ∀ y : ℝ, 0 ≤ y → y ≠ yr →
        retailerProfit μ p v w₁ w₂ y q < retailerProfit μ p v w₁ w₂ yr q := by
  have hFc := aux_rpa_cdf_continuous μ f hD
  have hwv : 0 < w₂ - v := by linarith
  set t := (w₂ - w₁) / (w₂ - v) with ht
  have hteq : (w₂ - v) * t = w₂ - w₁ := by rw [ht]; field_simp
  have hπ : (fun y : ℝ => retailerProfit μ p v w₁ w₂ y q) =
      fun y => (w₂ - w₁) * y - (w₂ - v) * (∫ x in (0 : ℝ)..y, cdf μ x) + (p - w₂) * S μ q := by
    funext y
    unfold retailerProfit S
    ring
  have hderiv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => retailerProfit μ p v w₁ w₂ y q)
      ((w₂ - w₁) - (w₂ - v) * cdf μ y) y := by
    intro y
    rw [hπ]
    have h1 : HasDerivAt (fun y : ℝ => (w₂ - w₁) * y) ((w₂ - w₁) * 1) y :=
      (hasDerivAt_id y).const_mul (w₂ - w₁)
    have h2 : HasDerivAt (fun y : ℝ => ∫ x in (0 : ℝ)..y, cdf μ x) (cdf μ y) y :=
      (hFc.integral_hasStrictDerivAt 0 y).hasDerivAt
    have h3 := (h1.sub (h2.const_mul (w₂ - v))).add_const ((p - w₂) * S μ q)
    simpa using h3
  have hdiff : ∀ y : ℝ, DifferentiableAt ℝ (fun y : ℝ => retailerProfit μ p v w₁ w₂ y q) y :=
    fun y => (hderiv y).differentiableAt
  have hcont : Continuous (fun y : ℝ => retailerProfit μ p v w₁ w₂ y q) :=
    continuous_iff_continuousAt.mpr fun y => (hdiff y).continuousAt
  have hd : ∀ y : ℝ, deriv (fun y : ℝ => retailerProfit μ p v w₁ w₂ y q) y =
      (w₂ - w₁) - (w₂ - v) * cdf μ y := fun y => (hderiv y).deriv
  refine ⟨?_, ?_, ?_⟩
  · apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0) hcont.continuousOn
      (fun y _ => (hdiff y).differentiableWithinAt)
    intro a _ b _ hab
    rw [hd, hd]
    have := monotone_cdf μ hab
    nlinarith
  · have ht0 : 0 ≤ t := div_nonneg (by linarith) hwv.le
    have ht1 : t < 1 := by rw [ht, div_lt_one hwv]; linarith
    obtain ⟨b, hb1, hb0⟩ :=
      (((tendsto_cdf_atTop μ).eventually (lt_mem_nhds ht1)).and
        (Filter.eventually_ge_atTop 0)).exists
    have hivt := intermediate_value_Icc hb0 hFc.continuousOn
    have hmem : t ∈ Set.Icc (cdf μ 0) (cdf μ b) := by
      rw [hD.cdf_zero]; exact ⟨ht0, hb1.le⟩
    obtain ⟨yr, hyr, hyrt⟩ := hivt hmem
    exact ⟨yr, hyr.1, hyrt⟩
  · intro yr hyr0 hyrt y hy0 hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmono : StrictMonoOn (fun y : ℝ => retailerProfit μ p v w₁ w₂ y q)
          (Set.Icc y yr) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc y yr) hcont.continuousOn
        intro x hx
        rw [interior_Icc] at hx
        rw [hd]
        have hFx : cdf μ x < cdf μ yr :=
          hD.strictMonoOn (Set.mem_Ici.mpr (by linarith [hx.1]))
            (Set.mem_Ici.mpr hyr0) hx.2
        rw [hyrt] at hFx
        nlinarith
      exact hmono ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
    · have hanti : StrictAntiOn (fun y : ℝ => retailerProfit μ p v w₁ w₂ y q)
          (Set.Icc yr y) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc yr y) hcont.continuousOn
        intro x hx
        rw [interior_Icc] at hx
        rw [hd]
        have hFx : cdf μ yr < cdf μ x :=
          hD.strictMonoOn (Set.mem_Ici.mpr hyr0)
            (Set.mem_Ici.mpr (by linarith [hx.1])) hx.1
        rw [hyrt] at hFx
        nlinarith
      exact hanti ⟨le_rfl, hgt.le⟩ ⟨hgt.le, le_rfl⟩ hgt
