-- Prove2me | solution 1 for CachonPushPull.Coordination.apd_pareto_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T02:42:49.130024+00:00
-- url     : https://prove2.me/submissions/b8478901-450b-498e-96eb-c8ca4f08780d

import Mathlib
import Definitions.Def_CachonPushPull_Coordination_Game



namespace CachonPushPull.Coordination

open MeasureTheory ProbabilityTheory Filter Topology

theorem apd_cdf_nonpos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (x : ℝ) (hx : x ≤ 0) : cdf μ x = 0 :=
  le_antisymm (hD.cdf_zero ▸ monotone_cdf μ hx) (cdf_nonneg μ x)

theorem apd_cdf_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) : Continuous (fun x => cdf μ x) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x 0 with h | h | h
  · have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds x] fun y => cdf μ y := by
      filter_upwards [Iio_mem_nhds h] with y hy
      exact (apd_cdf_nonpos μ f hD y (le_of_lt hy)).symm
    exact continuousAt_const.congr hev
  · subst h
    rw [continuousAt_iff_continuous_left_right]
    constructor
    · have h0 : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Set.Iic 0) 0 :=
        continuousWithinAt_const
      exact h0.congr (fun y hy => apd_cdf_nonpos μ f hD y hy)
        (apd_cdf_nonpos μ f hD 0 le_rfl)
    · exact (cdf μ).right_continuous 0
  · exact (hD.hasDerivAt x h).continuousAt

theorem apd_S_zero (μ : Measure ℝ) : S μ 0 = 0 := by simp [S]

theorem apd_S_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (y : ℝ) : HasDerivAt (S μ) (1 - cdf μ y) y := by
  have hFc := apd_cdf_cont μ f hD
  have h2 : HasDerivAt (fun y : ℝ => ∫ x in (0 : ℝ)..y, cdf μ x) (cdf μ y) y :=
    (hFc.integral_hasStrictDerivAt 0 y).hasDerivAt
  exact (hasDerivAt_id y).sub h2

theorem apd_S_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) : Continuous (S μ) :=
  continuous_iff_continuousAt.2 fun y => (apd_S_deriv μ f hD y).continuousAt

theorem apd_S_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ S μ y ∧ S μ y ≤ y ∧ y * (1 - cdf μ y) ≤ S μ y := by
  have hi : IntervalIntegrable (fun x => cdf μ x) volume 0 y :=
    (monotone_cdf μ).intervalIntegrable
  have h1 : (∫ x in (0 : ℝ)..y, cdf μ x) ≤ ∫ x in (0 : ℝ)..y, (1 : ℝ) :=
    intervalIntegral.integral_mono_on hy hi intervalIntegrable_const
      (fun x _ => cdf_le_one μ x)
  have h2 : (∫ x in (0 : ℝ)..y, cdf μ x) ≤ ∫ x in (0 : ℝ)..y, cdf μ y :=
    intervalIntegral.integral_mono_on hy hi intervalIntegrable_const
      (fun x hx => monotone_cdf μ hx.2)
  have h0 : 0 ≤ ∫ x in (0 : ℝ)..y, cdf μ x :=
    intervalIntegral.integral_nonneg hy (fun x _ => cdf_nonneg μ x)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h1 h2
  unfold S
  refine ⟨by linarith, by linarith, by nlinarith⟩

theorem apd_S_upper (μ : Measure ℝ) [IsProbabilityMeasure μ] (M y : ℝ) (hM : 0 ≤ M)
    (hMy : M ≤ y) : S μ y ≤ y * (1 - cdf μ M) + M := by
  have hi1 : IntervalIntegrable (fun x => cdf μ x) volume 0 M :=
    (monotone_cdf μ).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x => cdf μ x) volume M y :=
    (monotone_cdf μ).intervalIntegrable
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have h0 : 0 ≤ ∫ x in (0 : ℝ)..M, cdf μ x :=
    intervalIntegral.integral_nonneg hM (fun x _ => cdf_nonneg μ x)
  have h2 : (∫ x in M..y, cdf μ M) ≤ ∫ x in M..y, cdf μ x :=
    intervalIntegral.integral_mono_on hMy intervalIntegrable_const hi2
      (fun x hx => monotone_cdf μ hx.1)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h2
  have hF1 := cdf_le_one μ M
  have hF0 := cdf_nonneg μ M
  unfold S
  nlinarith


noncomputable def apdG (μ : Measure ℝ) (s k q : ℝ) : ℝ := s * S μ q - k * q

theorem apd_g_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (s k q : ℝ) :
    HasDerivAt (apdG μ s k) (s * (1 - cdf μ q) - k) q := by
  have h : HasDerivAt (fun y => s * S μ y - k * y) (s * (1 - cdf μ q) - k * 1) q :=
    ((apd_S_deriv μ f hD q).const_mul s).sub ((hasDerivAt_id' q).const_mul k)
  show HasDerivAt (fun y => s * S μ y - k * y) _ q
  exact h.congr_deriv (by ring)

theorem apd_g_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (s k : ℝ) : Continuous (apdG μ s k) :=
  continuous_iff_continuousAt.2 fun y => (apd_g_deriv μ f hD s k y).continuousAt

theorem gmax (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (s k z : ℝ) (hs : 0 ≤ s) (hz : s * (1 - cdf μ z) = k) :
    ∀ q, apdG μ s k q ≤ apdG μ s k z := by
  intro q
  have hd : ∀ x, deriv (apdG μ s k) x = s * (cdf μ z - cdf μ x) := by
    intro x; rw [(apd_g_deriv μ f hD s k x).deriv]; rw [← hz]; ring
  rcases le_total z q with h | h
  · have ha : AntitoneOn (apdG μ s k) (Set.Ici z) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici z) (apd_g_cont μ f hD s k).continuousOn
        (fun x _ => (apd_g_deriv μ f hD s k x).differentiableAt.differentiableWithinAt)
      intro x hx
      rw [interior_Ici] at hx
      rw [hd]
      have := monotone_cdf μ (le_of_lt (Set.mem_Ioi.1 hx))
      nlinarith
    exact ha (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h
  · have ha : MonotoneOn (apdG μ s k) (Set.Iic z) := by
      apply monotoneOn_of_deriv_nonneg (convex_Iic z) (apd_g_cont μ f hD s k).continuousOn
        (fun x _ => (apd_g_deriv μ f hD s k x).differentiableAt.differentiableWithinAt)
      intro x hx
      rw [interior_Iic] at hx
      rw [hd]
      have := monotone_cdf μ (le_of_lt (Set.mem_Iio.1 hx))
      nlinarith
    exact ha (Set.mem_Iic.2 h) (Set.mem_Iic.2 le_rfl) h

theorem gmax_strict (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (s k z : ℝ) (hs : 0 < s) (hz0 : 0 ≤ z)
    (hz : s * (1 - cdf μ z) = k) :
    ∀ a q, z ≤ a → a < q → apdG μ s k q < apdG μ s k a := by
  intro a q hza hq
  have hd : ∀ x, deriv (apdG μ s k) x = s * (cdf μ z - cdf μ x) := by
    intro x; rw [(apd_g_deriv μ f hD s k x).deriv]; rw [← hz]; ring
  have ha : StrictAntiOn (apdG μ s k) (Set.Ici z) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici z) (apd_g_cont μ f hD s k).continuousOn
    intro x hx
    rw [interior_Ici] at hx
    rw [hd]
    have := hD.strictMonoOn (Set.mem_Ici.2 hz0)
      (Set.mem_Ici.2 (hz0.trans (le_of_lt (Set.mem_Ioi.1 hx)))) (Set.mem_Ioi.1 hx)
    nlinarith
  exact ha (Set.mem_Ici.2 hza) (Set.mem_Ici.2 (hza.trans hq.le)) hq

theorem rp_eq (μ : Measure ℝ) (p v w₁ y q : ℝ) :
    retailerProfit μ p v w₁ p y q = apdG μ (p - v) (w₁ - v) y := by
  unfold retailerProfit apdG; ring

theorem sp_eq (μ : Measure ℝ) (p c v w₁ y q : ℝ) :
    supplierProfit μ p c v w₁ p y q = (w₁ - v) * y - (p - v) * S μ y + apdG μ (p - v) (c - v) q := by
  unfold supplierProfit apdG atOnceSales; simp; ring

theorem cp_eq (μ : Measure ℝ) (p c v q : ℝ) :
    chainProfit μ p c v q = apdG μ (p - v) (c - v) q := rfl

/-- sum of profits -/
theorem sum_le (μ : Measure ℝ) (p c v w₁ w₂ y q : ℝ) (hvc : v < c) (hyq : y ≤ q) :
    retailerProfit μ p v w₁ w₂ y q + supplierProfit μ p c v w₁ w₂ y q ≤
      max (chainProfit μ p c v q) (chainProfit μ p c v y) := by
  unfold retailerProfit supplierProfit atOnceSales chainProfit
  split_ifs
  · exact le_trans (le_of_eq (by ring)) (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    nlinarith

/-- outcome with contract (w1,p) -/
theorem outcome_of (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) (y : ℝ) (hy0 : 0 ≤ y) (hyq : y ≤ qo) :
    IsOutcome μ p c v (p - (p - v) * cdf μ y) p y qo := by
  have hpv : 0 < p - v := by linarith
  have hz : (p - v) * (1 - cdf μ qo) = c - v := by rw [hqo]; field_simp; ring
  have hm := gmax μ f hD (p - v) (c - v) qo hpv.le hz
  refine ⟨hy0, ⟨hyq, fun q' _ => ?_⟩, fun y' q' _ _ => ?_⟩
  · rw [sp_eq, sp_eq]; linarith [hm q']
  · rw [rp_eq, rp_eq]
    exact gmax μ f hD (p - v) _ y hpv.le (by ring) y'

theorem br_qo (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) (w₁ y : ℝ) (hyq : y ≤ qo) :
    IsSupplierBestResponse μ p c v w₁ p y qo := by
  have hpv : 0 < p - v := by linarith
  have hz : (p - v) * (1 - cdf μ qo) = c - v := by rw [hqo]; field_simp; ring
  have hm := gmax μ f hD (p - v) (c - v) qo hpv.le hz
  refine ⟨hyq, fun q' _ => ?_⟩
  rw [sp_eq, sp_eq]; linarith [hm q']

theorem qo_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) : 0 ≤ qo := by
  by_contra h
  push_neg at h
  have := apd_cdf_nonpos μ f hD qo h.le
  rw [hqo] at this
  have : 0 < (p - c) / (p - v) := div_pos (by linarith) (by linarith)
  linarith

theorem ivt_F (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (qo t : ℝ) (hq : 0 ≤ qo) (ht0 : 0 ≤ t) (ht : t ≤ cdf μ qo) :
    ∃ y, 0 ≤ y ∧ y ≤ qo ∧ cdf μ y = t := by
  have hmem : t ∈ Set.Icc (cdf μ 0) (cdf μ qo) := by rw [hD.cdf_zero]; exact ⟨ht0, ht⟩
  obtain ⟨y, hy, hyt⟩ := intermediate_value_Icc hq (apd_cdf_cont μ f hD).continuousOn hmem
  exact ⟨y, hy.1, hy.2, hyt⟩

theorem admissible_p (p c w₁ : ℝ) (h1 : c ≤ w₁) (h2 : w₁ ≤ p) : IsAdmissible p c w₁ p := by
  rcases h2.lt_or_eq with h | h
  · exact Or.inr (Or.inr ⟨h1, h, le_rfl⟩)
  · exact Or.inr (Or.inl ⟨h1, h, le_rfl⟩)

theorem part3 (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) :
    ∀ r : ℝ, 0 ≤ r → r ≤ chainProfit μ p c v qo →
      ∃ w₁ : ℝ, c ≤ w₁ ∧ w₁ ≤ p ∧ ∃ y q : ℝ, IsOutcome μ p c v w₁ p y q ∧
        retailerProfit μ p v w₁ p y q = r ∧
        supplierProfit μ p c v w₁ p y q = chainProfit μ p c v qo - r := by
  intro r hr0 hr1
  have hpv : 0 < p - v := by linarith
  have hq0 := qo_nonneg μ f hD p c v hvc hcp qo hqo
  have hFc := apd_cdf_cont μ f hD
  have hSc := apd_S_cont μ f hD
  set h : ℝ → ℝ := fun y => (p - v) * S μ y - (p - (p - v) * cdf μ y - v) * y with hh
  have hcont : Continuous h := by
    rw [hh]; fun_prop
  have h0 : h 0 = 0 := by simp [hh, apd_S_zero]
  have hqoe : h qo = chainProfit μ p c v qo := by
    simp only [hh, chainProfit, hqo]; field_simp; ring
  have hmem : r ∈ Set.Icc (h 0) (h qo) := by rw [h0, hqoe]; exact ⟨hr0, hr1⟩
  obtain ⟨y, hy, hyr⟩ := intermediate_value_Icc hq0 hcont.continuousOn hmem
  have hF1 : cdf μ y ≤ (p - c) / (p - v) := hqo ▸ monotone_cdf μ hy.2
  have hF0 := cdf_nonneg μ y
  have hmul : (p - v) * cdf μ y ≤ p - c := by
    have := mul_le_mul_of_nonneg_left hF1 hpv.le
    rwa [mul_div_cancel₀ _ hpv.ne'] at this
  refine ⟨p - (p - v) * cdf μ y, by linarith, by nlinarith, y, qo,
    outcome_of μ f hD p c v hvc hcp qo hqo y hy.1 hy.2, ?_, ?_⟩
  · rw [rp_eq, ← hyr]; simp only [hh, apdG]
  · rw [sp_eq, ← hyr, cp_eq]; simp only [hh, apdG]; ring

theorem apd_pareto_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) :
    (∀ w₁ : ℝ, c ≤ w₁ → w₁ ≤ p →
      (∃ y q : ℝ, IsOutcome μ p c v w₁ p y q) ∧ IsPareto μ p c v w₁ p) ∧
    (∀ w₁ w₂ : ℝ, IsPareto μ p c v w₁ w₂ →
      ∀ y q : ℝ, IsOutcome μ p c v w₁ w₂ y q →
        chainProfit μ p c v q = chainProfit μ p c v qo) ∧
    ∀ r : ℝ, 0 ≤ r → r ≤ chainProfit μ p c v qo →
      ∃ w₁ : ℝ, c ≤ w₁ ∧ w₁ ≤ p ∧ ∃ y q : ℝ, IsOutcome μ p c v w₁ p y q ∧
        retailerProfit μ p v w₁ p y q = r ∧
        supplierProfit μ p c v w₁ p y q = chainProfit μ p c v qo - r := by
  have hpv : 0 < p - v := by linarith
  have hq0 := qo_nonneg μ f hD p c v hvc hcp qo hqo
  have hz : (p - v) * (1 - cdf μ qo) = c - v := by rw [hqo]; field_simp; ring
  have hPi : ∀ q, chainProfit μ p c v q ≤ chainProfit μ p c v qo := by
    intro q; rw [cp_eq, cp_eq]; exact gmax μ f hD (p - v) (c - v) qo hpv.le hz q
  -- total of any outcome
  have htot : ∀ w₁ w₂ y q, y ≤ q →
      retailerProfit μ p v w₁ w₂ y q + supplierProfit μ p c v w₁ w₂ y q ≤
        chainProfit μ p c v qo := by
    intro w₁ w₂ y q hyq
    exact (sum_le μ p c v w₁ w₂ y q hvc hyq).trans (max_le (hPi q) (hPi y))
  have P3 := part3 μ f hD p c v hvc hcp qo hqo
  refine ⟨?_, ?_, P3⟩
  · intro w₁ hc1 h1p
    have hpw : (p - w₁) / (p - v) ≤ cdf μ qo := by
      rw [hqo]; exact div_le_div_of_nonneg_right (by linarith) hpv.le
    obtain ⟨yr, hyr0, hyrq, hyrF⟩ := ivt_F μ f hD qo _ hq0 (div_nonneg (by linarith) hpv.le) hpw
    have hw : p - (p - v) * cdf μ yr = w₁ := by rw [hyrF]; field_simp; ring
    have hout := outcome_of μ f hD p c v hvc hcp qo hqo yr hyr0 hyrq
    rw [hw] at hout
    refine ⟨⟨yr, qo, hout⟩, admissible_p p c w₁ hc1 h1p, ?_⟩
    rintro y q ⟨hy0, ⟨hyq, hbr⟩, hopt⟩ ⟨w₁', w₂', y', q', hadm, hout', hdom⟩
    have hsum : ∀ a b, retailerProfit μ p v w₁ p a b + supplierProfit μ p c v w₁ p a b =
        chainProfit μ p c v b := by
      intro a b; rw [rp_eq, sp_eq, cp_eq]; unfold apdG; ring
    have hyqo : y ≤ qo := by
      by_contra hlt
      push_neg at hlt
      have h1 := hopt qo qo hq0 (br_qo μ f hD p c v hvc hcp qo hqo w₁ qo le_rfl)
      rw [rp_eq, rp_eq] at h1
      have h2 := gmax_strict μ f hD (p - v) (w₁ - v) yr hpv hyr0
        (by rw [hyrF]; field_simp; ring) qo y hyrq hlt
      linarith
    have h3 := hbr qo hyqo
    rw [sp_eq, sp_eq] at h3
    have h4 : chainProfit μ p c v qo ≤ chainProfit μ p c v q := by
      rw [cp_eq, cp_eq]; linarith
    have h5 := hPi q
    have h6 := htot w₁' w₂' y' q' hout'.2.1.1
    have h7 := hsum y q
    obtain ⟨d1, d2, d3⟩ := hdom
    rcases d3 with d3 | d3 <;> linarith
  · intro w₁ w₂ hP y q hout
    obtain ⟨hy0, ⟨hyq, hbr⟩, hopt⟩ := hout
    have hcw : c ≤ w₁ ∧ c ≤ w₂ := by
      rcases hP.1 with ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩
      · exact ⟨a, by linarith⟩
      · exact ⟨a, by linarith⟩
      · exact ⟨a, by linarith⟩
    -- total
    have hsum : retailerProfit μ p v w₁ w₂ y q + supplierProfit μ p c v w₁ w₂ y q =
        chainProfit μ p c v q := by
      by_cases hw : w₂ ≤ p
      · unfold retailerProfit supplierProfit atOnceSales chainProfit
        simp only [if_pos hw]; ring
      · have h1 := hbr y le_rfl
        unfold supplierProfit atOnceSales at h1
        simp only [if_neg hw] at h1
        have hqy : q = y := by
          have : (c - v) * q ≤ (c - v) * y := by linarith
          have := le_of_mul_le_mul_left this (by linarith)
          linarith
        subst hqy
        unfold retailerProfit supplierProfit atOnceSales chainProfit
        simp only [if_neg hw]; ring
    have hs0 : 0 ≤ supplierProfit μ p c v w₁ w₂ y q := by
      have h1 := hbr y le_rfl
      have : supplierProfit μ p c v w₁ w₂ y y = (w₁ - c) * y := by
        unfold supplierProfit atOnceSales; split_ifs <;> ring
      have : 0 ≤ (w₁ - c) * y := mul_nonneg (by linarith [hcw.1]) hy0
      linarith
    have hr0 : 0 ≤ retailerProfit μ p v w₁ w₂ y q := by
      by_cases hw : w₂ ≤ p
      · have hwv : 0 < w₂ - v := by linarith [hcw.2]
        have hle : (w₂ - c) / (w₂ - v) ≤ cdf μ qo := by
          rw [hqo, div_le_div_iff₀ hwv hpv]; nlinarith [hcw.2]
        obtain ⟨za, hza0, -, hzaF⟩ := ivt_F μ f hD qo _ hq0
          (div_nonneg (by linarith [hcw.2]) hwv.le) hle
        have hbr0 : IsSupplierBestResponse μ p c v w₁ w₂ 0 za := by
          refine ⟨hza0, fun q' _ => ?_⟩
          have hm := gmax μ f hD (w₂ - v) (c - v) za hwv.le
            (by rw [hzaF]; field_simp; ring) q'
          unfold supplierProfit atOnceSales
          simp only [if_pos hw]
          unfold apdG at hm
          simp only [apd_S_zero]
          linarith
        have h1 := hopt 0 za le_rfl hbr0
        have h2 : retailerProfit μ p v w₁ w₂ 0 za = (p - w₂) * S μ za := by
          unfold retailerProfit atOnceSales; simp only [if_pos hw]; simp [apd_S_zero]
        have h3 := (apd_S_bounds μ za hza0).1
        have h4 : 0 ≤ (p - w₂) * S μ za := mul_nonneg (by linarith) h3
        linarith
      · have hbr0 : IsSupplierBestResponse μ p c v w₁ w₂ 0 0 := by
          refine ⟨le_rfl, fun q' hq' => ?_⟩
          unfold supplierProfit atOnceSales
          simp only [if_neg hw]
          nlinarith
        have h1 := hopt 0 0 le_rfl hbr0
        have h2 : retailerProfit μ p v w₁ w₂ 0 0 = 0 := by
          unfold retailerProfit atOnceSales; simp only [if_neg hw]; simp [apd_S_zero]
        linarith
    by_contra hne
    have hlt : chainProfit μ p c v q < chainProfit μ p c v qo := lt_of_le_of_ne (hPi q) hne
    obtain ⟨w₁', hw1, hw2, y', q', hout', hR, hS⟩ :=
      P3 (retailerProfit μ p v w₁ w₂ y q) hr0 (by linarith)
    apply hP.2 y q ⟨hy0, ⟨hyq, hbr⟩, hopt⟩
    refine ⟨w₁', p, y', q', admissible_p p c w₁' hw1 hw2, hout', ?_, ?_, Or.inr ?_⟩
    · rw [hR]
    · rw [hS]; linarith
    · rw [hS]; linarith

end CachonPushPull.Coordination

open CachonPushPull.Coordination
open CachonPushPull.Coordination MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) :
    (∀ w₁ : ℝ, c ≤ w₁ → w₁ ≤ p →
      (∃ y q : ℝ, IsOutcome μ p c v w₁ p y q) ∧ IsPareto μ p c v w₁ p) ∧
    (∀ w₁ w₂ : ℝ, IsPareto μ p c v w₁ w₂ →
      ∀ y q : ℝ, IsOutcome μ p c v w₁ w₂ y q →
        chainProfit μ p c v q = chainProfit μ p c v qo) ∧
    ∀ r : ℝ, 0 ≤ r → r ≤ chainProfit μ p c v qo →
      ∃ w₁ : ℝ, c ≤ w₁ ∧ w₁ ≤ p ∧ ∃ y q : ℝ, IsOutcome μ p c v w₁ p y q ∧
        retailerProfit μ p v w₁ p y q = r ∧
        supplierProfit μ p c v w₁ p y q = chainProfit μ p c v qo - r := by
  exact apd_pareto_core μ f hD p c v hvc hcp qo hqo
