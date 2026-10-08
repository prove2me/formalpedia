-- Prove2me | solution 1 for CachonPushPull.Coordination.retailer_prebook_argmax
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:13:25.514714+00:00
-- url     : https://prove2.me/submissions/afb6defd-e74e-48c0-92ac-dd46efeb21d0

import Mathlib
import Definitions.Def_CachonPushPull_Coordination_Game

set_option autoImplicit false

namespace CachonD7d78e25

open MeasureTheory ProbabilityTheory CachonPushPull.Coordination Filter Topology Set

lemma cdf_nonpos {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ} (hD : DemandModel μ f)
    {x : ℝ} (hx : x ≤ 0) : cdf μ x = 0 :=
  le_antisymm (hD.cdf_zero ▸ (cdf μ).mono hx) (cdf_nonneg μ x)

lemma cdf_continuous {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hD : DemandModel μ f) : Continuous (cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have : (cdf μ : ℝ → ℝ) =ᶠ[nhds x] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with z hz using cdf_nonpos hD (le_of_lt hz)
    exact (continuousAt_const).congr this.symm
  · rw [continuousAt_iff_continuous_left_right]
    constructor
    · have h : ContinuousWithinAt (fun _ : ℝ => (0:ℝ)) (Set.Iic (0:ℝ)) (0:ℝ) :=
        continuousWithinAt_const
      exact h.congr (fun z hz => cdf_nonpos hD (x := z) (Set.mem_Iic.1 hz))
        (cdf_nonpos hD (x := 0) le_rfl)
    · exact (cdf μ).right_continuous 0
  · exact (hD.hasDerivAt x hx).continuousAt

lemma S_hasDerivAt {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hD : DemandModel μ f) (q : ℝ) : HasDerivAt (S μ) (1 - cdf μ q) q := by
  have h1 := ((cdf_continuous hD).integral_hasStrictDerivAt 0 q).hasDerivAt
  show HasDerivAt (fun q => q - ∫ x in (0:ℝ)..q, cdf μ x) _ q
  exact (hasDerivAt_id' q).sub h1

lemma rp_hasDerivAt {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hD : DemandModel μ f) {p v w₁ w₂ : ℝ} (hw : w₂ ≤ p) (q y : ℝ) :
    HasDerivAt (fun y => retailerProfit μ p v w₁ w₂ y q)
      ((w₂ - w₁) - (w₂ - v) * cdf μ y) y := by
  have h : (fun y => retailerProfit μ p v w₁ w₂ y q) =
      fun y => -(w₁ - v) * y + (p - v) * S μ y + (p - w₂) * (S μ q - S μ y) := by
    funext y; simp [retailerProfit, atOnceSales, hw]
  rw [h]
  have := ((((hasDerivAt_id' y).const_mul (-(w₁ - v))).add
    ((S_hasDerivAt hD y).const_mul (p - v))).add
    (((S_hasDerivAt hD y).const_sub (S μ q)).const_mul (p - w₂)))
  exact this.congr_deriv (by ring)

lemma rp_deriv {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hD : DemandModel μ f) {p v w₁ w₂ : ℝ} (hw : w₂ ≤ p) (q y : ℝ) :
    deriv (fun y => retailerProfit μ p v w₁ w₂ y q) y = (w₂ - w₁) - (w₂ - v) * cdf μ y :=
  (rp_hasDerivAt hD hw q y).deriv

lemma rp_continuous {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hD : DemandModel μ f) {p v w₁ w₂ : ℝ} (hw : w₂ ≤ p) (q : ℝ) :
    Continuous (fun y => retailerProfit μ p v w₁ w₂ y q) :=
  continuous_iff_continuousAt.2 fun y => (rp_hasDerivAt hD hw q y).continuousAt

end CachonD7d78e25

open MeasureTheory ProbabilityTheory CachonPushPull.Coordination in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (w₁ w₂ : ℝ) (hcw₁ : c ≤ w₁) (hw₁₂ : w₁ ≤ w₂) (hw₂p : w₂ ≤ p) (q : ℝ) :
    ConcaveOn ℝ (Set.Ici 0) (fun y : ℝ => retailerProfit μ p v w₁ w₂ y q) ∧
    (∃ yr : ℝ, 0 ≤ yr ∧ cdf μ yr = (w₂ - w₁) / (w₂ - v)) ∧
    ∀ yr : ℝ, 0 ≤ yr → cdf μ yr = (w₂ - w₁) / (w₂ - v) →
      ∀ y : ℝ, 0 ≤ y → y ≠ yr →
        retailerProfit μ p v w₁ w₂ y q < retailerProfit μ p v w₁ w₂ yr q := by
  have hwv : 0 < w₂ - v := by linarith
  have ht0 : 0 ≤ (w₂ - w₁) / (w₂ - v) := div_nonneg (by linarith) hwv.le
  have ht1 : (w₂ - w₁) / (w₂ - v) < 1 := (div_lt_one hwv).2 (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
      (CachonD7d78e25.rp_continuous hD hw₂p q).continuousOn
    · intro x _
      exact (CachonD7d78e25.rp_hasDerivAt hD hw₂p q x).differentiableAt.differentiableWithinAt
    · intro x _ y _ hxy
      simp only [CachonD7d78e25.rp_deriv hD hw₂p]
      have := monotone_cdf μ hxy
      nlinarith
  · obtain ⟨N, hN⟩ := ((tendsto_cdf_atTop (μ := μ)).eventually (lt_mem_nhds ht1)).and
      (Filter.eventually_ge_atTop 0) |>.exists
    have hsub := intermediate_value_Icc hN.2 (CachonD7d78e25.cdf_continuous hD).continuousOn
    obtain ⟨y, hy, hy'⟩ := hsub ⟨by rw [hD.cdf_zero]; exact ht0, hN.1.le⟩
    exact ⟨y, hy.1, hy'⟩
  · intro yr hyr h y hy hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmono : StrictMonoOn (fun y => retailerProfit μ p v w₁ w₂ y q)
          (Set.Icc 0 yr) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc 0 yr)
          (CachonD7d78e25.rp_continuous hD hw₂p q).continuousOn
        intro x hx
        rw [interior_Icc] at hx
        rw [CachonD7d78e25.rp_deriv hD hw₂p]
        have hlt' : cdf μ x < cdf μ yr := hD.strictMonoOn (le_of_lt hx.1) hyr hx.2
        rw [h] at hlt'
        have : (w₂ - v) * cdf μ x < (w₂ - v) * ((w₂ - w₁) / (w₂ - v)) :=
          mul_lt_mul_of_pos_left hlt' hwv
        rw [mul_div_cancel₀ _ hwv.ne'] at this
        linarith
      exact hmono ⟨hy, hlt.le⟩ ⟨hyr, le_rfl⟩ hlt
    · have hanti : StrictAntiOn (fun y => retailerProfit μ p v w₁ w₂ y q)
          (Set.Ici yr) := by
        apply strictAntiOn_of_deriv_neg (convex_Ici yr)
          (CachonD7d78e25.rp_continuous hD hw₂p q).continuousOn
        intro x hx
        rw [interior_Ici] at hx
        rw [CachonD7d78e25.rp_deriv hD hw₂p]
        have hlt' : cdf μ yr < cdf μ x := hD.strictMonoOn hyr (hyr.trans (le_of_lt hx)) hx
        rw [h] at hlt'
        have : (w₂ - v) * ((w₂ - w₁) / (w₂ - v)) < (w₂ - v) * cdf μ x :=
          mul_lt_mul_of_pos_left hlt' hwv
        rw [mul_div_cancel₀ _ hwv.ne'] at this
        linarith
      exact hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hgt.le) hgt
