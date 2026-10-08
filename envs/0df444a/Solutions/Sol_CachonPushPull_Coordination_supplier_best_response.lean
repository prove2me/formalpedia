-- Prove2me | solution 1 for CachonPushPull.Coordination.supplier_best_response
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T08:27:32.573618+00:00
-- url     : https://prove2.me/submissions/db8fe4d5-f436-4fb7-9654-42cb5e02e83a

import Mathlib
import Definitions.Def_CachonPushPull_Coordination_Game

set_option autoImplicit false

namespace CachonPushPull.Coordination.SBRHelp

open MeasureTheory ProbabilityTheory CachonPushPull.Coordination

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
    · have h : ContinuousWithinAt (fun _ : ℝ => (0:ℝ)) (Set.Iic (0:ℝ)) (0:ℝ) := continuousWithinAt_const
      exact h.congr (fun z hz => cdf_nonpos hD (x := z) (Set.mem_Iic.1 hz)) (cdf_nonpos hD (x := 0) le_rfl)
    · exact (cdf μ).right_continuous 0
  · exact (hD.hasDerivAt x hx).continuousAt

lemma S_hasDerivAt {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hD : DemandModel μ f) (q : ℝ) : HasDerivAt (S μ) (1 - cdf μ q) q := by
  have h1 := ((cdf_continuous hD).integral_hasStrictDerivAt 0 q).hasDerivAt
  show HasDerivAt (fun q => q - ∫ x in (0:ℝ)..q, cdf μ x) _ q
  exact (hasDerivAt_id' q).sub h1

lemma prof_hasDerivAt {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hD : DemandModel μ f) {p c v w₁ w₂ : ℝ} (hw : w₂ ≤ p) (y q : ℝ) :
    HasDerivAt (supplierProfit μ p c v w₁ w₂ y) ((w₂ - v) * (1 - cdf μ q) - (c - v)) q := by
  have h : supplierProfit μ p c v w₁ w₂ y =
      fun q => (w₁ - v) * y + (w₂ - v) * (S μ q - S μ y) - (c - v) * q := by
    funext q; simp [supplierProfit, atOnceSales, hw]
  rw [h]
  have := ((((S_hasDerivAt hD q).sub_const (S μ y)).const_mul (w₂ - v)).const_add
    ((w₁ - v) * y)).sub ((hasDerivAt_id' q).const_mul (c - v))
  exact this.congr_deriv (by ring)

end CachonPushPull.Coordination.SBRHelp

open MeasureTheory ProbabilityTheory CachonPushPull.Coordination in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (w₁ w₂ : ℝ) (hcw₂ : c ≤ w₂) (hw₂p : w₂ ≤ p) :
    (∃ qs : ℝ, 0 ≤ qs ∧ cdf μ qs = (w₂ - c) / (w₂ - v)) ∧
    ∀ y : ℝ, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici y) (supplierProfit μ p c v w₁ w₂ y) ∧
      ∀ qs : ℝ, 0 ≤ qs → cdf μ qs = (w₂ - c) / (w₂ - v) →
        ∀ q : ℝ, IsSupplierBestResponse μ p c v w₁ w₂ y q ↔ q = max y qs := by
  have hwv : 0 < w₂ - v := by linarith
  set t := (w₂ - c) / (w₂ - v) with ht
  have key : (w₂ - v) * t = w₂ - c := by rw [ht]; field_simp
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hwv.le
  have ht1 : t < 1 := by rw [div_lt_one hwv]; linarith
  have hF := SBRHelp.cdf_continuous hD
  have hmono : Monotone (cdf μ) := (cdf μ).mono
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb, hb0⟩ :=
      (((tendsto_order.1 (tendsto_cdf_atTop μ)).1 t ht1).and (Filter.eventually_ge_atTop 0)).exists
    have hsub := intermediate_value_Icc hb0 hF.continuousOn
    rw [hD.cdf_zero] at hsub
    obtain ⟨qs, hqs, hqst⟩ := hsub ⟨ht0, hb.le⟩
    exact ⟨qs, hqs.1, hqst⟩
  · intro y hy
    have hd := fun q => SBRHelp.prof_hasDerivAt hD (w₁ := w₁) (c := c) (v := v) hw₂p y q
    have hderiv : deriv (supplierProfit μ p c v w₁ w₂ y) =
        fun q => (w₂ - v) * (1 - cdf μ q) - (c - v) := funext fun q => (hd q).deriv
    have hcont : Continuous (supplierProfit μ p c v w₁ w₂ y) :=
      continuous_iff_continuousAt.2 fun q => (hd q).continuousAt
    refine ⟨?_, ?_⟩
    · apply AntitoneOn.concaveOn_of_deriv (convex_Ici y) hcont.continuousOn
      · exact fun q _ => (hd q).differentiableAt.differentiableWithinAt
      · rw [hderiv]
        intro a _ b _ hab
        have := mul_le_mul_of_nonneg_left (hmono hab) hwv.le
        dsimp only
        nlinarith
    · intro qs hqs0 hqs q
      set φ := supplierProfit μ p c v w₁ w₂ y with hφ
      have inc : StrictMonoOn φ (Set.Icc 0 qs) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc 0 qs) hcont.continuousOn
        intro x hx
        rw [interior_Icc] at hx
        rw [hderiv]
        have hlt : cdf μ x < t := hqs ▸ hD.strictMonoOn (Set.mem_Ici.2 hx.1.le)
          (Set.mem_Ici.2 hqs0) hx.2
        have := mul_lt_mul_of_pos_left hlt hwv
        dsimp only
        nlinarith
      have dec : StrictAntiOn φ (Set.Ici qs) := by
        apply strictAntiOn_of_deriv_neg (convex_Ici qs) hcont.continuousOn
        intro x hx
        rw [interior_Ici] at hx
        rw [hderiv]
        have hlt : t < cdf μ x := hqs ▸ hD.strictMonoOn (Set.mem_Ici.2 hqs0)
          (Set.mem_Ici.2 (hqs0.trans hx.le)) hx
        have := mul_lt_mul_of_pos_left hlt hwv
        dsimp only
        nlinarith
      constructor
      · rintro ⟨hyq, hmax⟩
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hm : max y qs = qs := by
            rcases le_total y qs with h | h
            · exact max_eq_right h
            · rw [max_eq_left h] at hlt; linarith
          rw [hm] at hlt
          have h1 := inc ⟨hy.trans hyq, hlt.le⟩ ⟨hqs0, le_rfl⟩ hlt
          have h2 := hmax qs (le_trans (le_max_left y qs) hm.le)
          linarith
        · have h1 := dec (Set.mem_Ici.2 (le_max_right y qs))
            (Set.mem_Ici.2 ((le_max_right y qs).trans hgt.le)) hgt
          have h2 := hmax (max y qs) (le_max_left y qs)
          linarith
      · rintro rfl
        refine ⟨le_max_left y qs, fun q' hq' => ?_⟩
        rcases le_total q' qs with h | h
        · have hm : max y qs = qs := max_eq_right (hq'.trans h)
          rw [hm]
          exact inc.monotoneOn ⟨hy.trans hq', h⟩ ⟨hqs0, le_rfl⟩ h
        · exact dec.antitoneOn (Set.mem_Ici.2 (le_max_right y qs)) (Set.mem_Ici.2 h)
            (max_le hq' h)
