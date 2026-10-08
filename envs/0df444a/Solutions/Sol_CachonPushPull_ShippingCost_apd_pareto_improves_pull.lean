-- Prove2me | solution 1 for CachonPushPull.ShippingCost.apd_pareto_improves_pull
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T02:32:30.871091+00:00
-- url     : https://prove2.me/submissions/86e69b72-1812-4de3-9d31-b69b39c6a7da

import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game



namespace CachonPushPull.ShippingCost

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

theorem apd_Lpos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (A B M : ℝ) (hA : 0 < A) (hBA : B < A) (hM : 0 < M) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ M ∧ B * ε < A * S μ ε := by
  have ht : (0 : ℝ) < (A - B) / A := div_pos (by linarith) hA
  have hc : Tendsto (fun x => cdf μ x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ((apd_cdf_cont μ f hD).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rwa [hD.cdf_zero] at this
  obtain ⟨ε, hε1, hε2⟩ := ((hc.eventually (gt_mem_nhds ht)).and
    (Ioo_mem_nhdsGT hM)).exists
  refine ⟨ε, hε2.1, hε2.2.le, ?_⟩
  obtain ⟨_, _, h3⟩ := apd_S_bounds μ ε hε2.1.le
  have h4 : A * cdf μ ε < A - B := by
    have := (lt_div_iff₀ hA).1 hε1
    linarith
  have h5 : B * ε < A * (ε * (1 - cdf μ ε)) := by nlinarith [hε2.1]
  nlinarith

noncomputable def apdG (μ : Measure ℝ) (s k q : ℝ) : ℝ := s * S μ q - k * q

theorem apd_sp_eq (μ : Measure ℝ) (c v τ w₁ w₂ y q : ℝ) :
    supplierProfit μ c v τ w₁ w₂ y q =
      (w₁ - v) * y - (w₂ - τ - v) * S μ y + apdG μ (w₂ - τ - v) (c - v) q := by
  unfold supplierProfit apdG; ring

theorem apd_br_iff (μ : Measure ℝ) (c v τ w₁ w₂ y q : ℝ) :
    IsSupplierBestResponse μ c v τ w₁ w₂ y q ↔
      y ≤ q ∧ ∀ q', y ≤ q' → apdG μ (w₂ - τ - v) (c - v) q' ≤ apdG μ (w₂ - τ - v) (c - v) q := by
  unfold IsSupplierBestResponse
  simp only [apd_sp_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun q' hq' => by have := h2 q' hq'; linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun q' hq' => by have := h2 q' hq'; linarith⟩

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

theorem apd_cdf_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (x : ℝ) (hx : 0 < x) : 0 < cdf μ x := by
  have := hD.strictMonoOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx.le) hx
  rwa [hD.cdf_zero] at this

theorem apd_g_anti (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (s k : ℝ) (hk : 0 < k) (hsk : s ≤ k) :
    StrictAntiOn (apdG μ s k) (Set.Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0) (apd_g_cont μ f hD s k).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  rw [(apd_g_deriv μ f hD s k x).deriv]
  have h1 := apd_cdf_pos μ f hD x hx
  have h2 := cdf_le_one μ x
  rcases le_or_gt s 0 with hs | hs
  · nlinarith
  · nlinarith

theorem apd_g_sconc (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (s k : ℝ) (hs : 0 < s) :
    StrictConcaveOn ℝ (Set.Ici 0) (apdG μ s k) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0)
    (apd_g_cont μ f hD s k).continuousOn
  intro a ha b hb hab
  rw [interior_Ici] at ha hb
  rw [(apd_g_deriv μ f hD s k a).deriv, (apd_g_deriv μ f hD s k b).deriv]
  have := hD.strictMonoOn (Set.mem_Ici.2 (le_of_lt ha)) (Set.mem_Ici.2 (le_of_lt hb)) hab
  nlinarith

/-- uniqueness of maximizer over `[y, ∞)` -/
theorem apd_g_uniq (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (s k : ℝ) (hs : 0 < s) (y a b : ℝ) (hy : 0 ≤ y)
    (ha : y ≤ a ∧ ∀ q', y ≤ q' → apdG μ s k q' ≤ apdG μ s k a)
    (hb : y ≤ b ∧ ∀ q', y ≤ q' → apdG μ s k q' ≤ apdG μ s k b) : a = b := by
  by_contra hne
  have hc := (apd_g_sconc μ f hD s k hs).2 (Set.mem_Ici.2 (hy.trans ha.1))
    (Set.mem_Ici.2 (hy.trans hb.1)) hne (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num)
  simp only [smul_eq_mul] at hc
  have h1 := ha.2 (1/2 * a + 1/2 * b) (by linarith [ha.1, hb.1])
  have h2 := hb.2 (1/2 * a + 1/2 * b) (by linarith [ha.1, hb.1])
  linarith

theorem apd_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (τ : ℝ) (hτ : 0 < τ) (w₂ : ℝ) (hw₂p : w₂ < p)
    (hpull : PullNoPrebook μ p c v τ w₂) :
    ∃ w₁ : ℝ, c < w₁ ∧ w₁ < w₂ ∧
      (∃ y q : ℝ, IsOutcome μ p c v τ w₁ w₂ y q) ∧
      ∀ y q : ℝ, IsOutcome μ p c v τ w₁ w₂ y q →
        ∀ q₀ : ℝ, IsSupplierBestResponse μ c v τ w₂ w₂ 0 q₀ →
          retailerProfit μ p v w₂ w₂ 0 q₀ < retailerProfit μ p v w₁ w₂ y q ∧
          supplierProfit μ c v τ w₂ w₂ 0 q₀ < supplierProfit μ c v τ w₁ w₂ y q := by
  obtain ⟨r, hr, hnp⟩ := hpull
  obtain ⟨s, hs⟩ : ∃ s, w₂ - τ - v = s := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, c - v = k := ⟨_, rfl⟩
  have hBR : ∀ w y q, IsSupplierBestResponse μ c v τ w w₂ y q ↔
      y ≤ q ∧ ∀ q', y ≤ q' → apdG μ s k q' ≤ apdG μ s k q := by
    intro w y q; rw [apd_br_iff, hs, hk]
  have hSP : ∀ w y q, supplierProfit μ c v τ w w₂ y q =
      (w - v) * y - s * S μ y + apdG μ s k q := by
    intro w y q; rw [apd_sp_eq, hs, hk]
  have hk0 : 0 < k := by linarith
  have hS0 := apd_S_zero μ
  have hG0 : apdG μ s k 0 = 0 := by simp [apdG, hS0]
  have hr' := (hBR w₂ 0 r).1 hr
  -- Step 1: k < s
  have hsk : k < s := by
    by_contra hle
    push_neg at hle
    have hanti := apd_g_anti μ f hD s k hk0 hle
    have hr0 : r = 0 := by
      rcases hr'.1.lt_or_eq with h | h
      · exfalso
        have h1 := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h.le) h
        have h2 := hr'.2 0 le_rfl
        linarith
      · exact h.symm
    obtain ⟨ε, hε, -, hεS⟩ := apd_Lpos μ f hD (p - v) (w₂ - v) 1 (by linarith) (by linarith) one_pos
    have hbr : IsSupplierBestResponse μ c v τ w₂ w₂ ε ε :=
      (hBR _ _ _).2 ⟨le_rfl, fun q' hq' =>
        hanti.antitoneOn (Set.mem_Ici.2 hε.le) (Set.mem_Ici.2 (hε.le.trans hq')) hq'⟩
    have := hnp ε ε hε hbr
    rw [hr0] at this
    unfold retailerProfit at this
    rw [hS0] at this
    linarith
  have hs0 : 0 < s := by linarith
  have hconc := apd_g_sconc μ f hD s k hs0
  have hrpos : 0 < r := by
    rcases hr'.1.lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨ε, hε, -, hεS⟩ := apd_Lpos μ f hD s k 1 hs0 hsk one_pos
      have h1 := hr'.2 ε hε.le
      rw [← h, hG0] at h1
      unfold apdG at h1
      linarith
  have hcw : c < w₂ := by linarith
  -- Step 3: best responses
  have hBRex : ∀ w y, 0 ≤ y → IsSupplierBestResponse μ c v τ w w₂ y (max y r) := by
    intro w y hy
    rw [hBR]
    rcases le_total y r with h | h
    · rw [max_eq_right h]
      exact ⟨h, fun q' hq' => hr'.2 q' (hy.trans hq')⟩
    · rw [max_eq_left h]
      refine ⟨le_rfl, fun q' hq' => ?_⟩
      have hseg : y ∈ segment ℝ r q' := by
        rw [segment_eq_Icc (h.trans hq')]; exact ⟨h, hq'⟩
      have := hconc.concaveOn.ge_on_segment (Set.mem_Ici.2 hr'.1)
        (Set.mem_Ici.2 (hy.trans hq')) hseg
      have h2 := hr'.2 q' (hy.trans hq')
      rw [min_eq_right h2] at this
      exact this
  have hBRuniq : ∀ w y q, 0 ≤ y → IsSupplierBestResponse μ c v τ w w₂ y q → q = max y r := by
    intro w y q hy hq
    exact apd_g_uniq μ f hD s k hs0 y q (max y r) hy ((hBR w y q).1 hq)
      ((hBR w y _).1 (hBRex w y hy))
  -- Step 4: choose w₁
  set w₁ := (max c (w₂ - τ) + w₂) / 2 with hw₁
  have hcw₁ : c < w₁ := by
    have := le_max_left c (w₂ - τ); rw [hw₁]; linarith
  have hτw₁ : w₂ - τ < w₁ := by
    have := le_max_right c (w₂ - τ); rw [hw₁]; linarith
  have hw₁w₂ : w₁ < w₂ := by
    have : max c (w₂ - τ) < w₂ := max_lt hcw (by linarith)
    rw [hw₁]; linarith
  clear_value w₁
  have hSc := apd_S_cont μ f hD
  set H : ℝ → ℝ := fun y => retailerProfit μ p v w₁ w₂ y (max y r) with hH
  have hHc : Continuous H := by
    rw [hH]; unfold retailerProfit
    exact ((continuous_const.mul continuous_id).add (continuous_const.mul hSc)).add
      (continuous_const.mul ((hSc.comp (continuous_id.max continuous_const)).sub hSc))
  -- Step 5: coercivity
  have hpv : 0 < p - v := by linarith
  have hδ : 0 < (w₁ - v) / (2 * (p - v)) := div_pos (by linarith) (by linarith)
  obtain ⟨M, hM1, hM0⟩ := (((tendsto_cdf_atTop μ).eventually
    (lt_mem_nhds (by linarith : 1 - (w₁ - v) / (2 * (p - v)) < 1))).and
    (eventually_ge_atTop 0)).exists
  have hMb : (p - v) * (1 - cdf μ M) ≤ (w₁ - v) / 2 := by
    have : (p - v) * ((w₁ - v) / (2 * (p - v))) = (w₁ - v) / 2 := by field_simp
    nlinarith
  have hbig : ∀ y, max M r ≤ y → H y ≤ -((w₁ - v) / 2) * y + (p - v) * M := by
    intro y hy
    have hMy : M ≤ y := (le_max_left _ _).trans hy
    have hry : r ≤ y := (le_max_right _ _).trans hy
    have hy0 : 0 ≤ y := hM0.trans hMy
    have hup := apd_S_upper μ M y hM0 hMy
    simp only [hH, retailerProfit, max_eq_left hry]
    have h3 : (p - v) * (y * (1 - cdf μ M)) ≤ y * ((w₁ - v) / 2) := by
      have := mul_le_mul_of_nonneg_left hMb hy0; nlinarith
    nlinarith
  set Y := max (max M r) (2 * ((p - v) * M - H 0) / (w₁ - v)) with hY
  have hY0 : 0 ≤ Y := (hM0.trans (le_max_left _ _)).trans (le_max_left _ _)
  have hfar : ∀ y, Y ≤ y → H y ≤ H 0 := by
    intro y hy
    have h1 := hbig y ((le_max_left _ _).trans hy)
    have h2 : 2 * ((p - v) * M - H 0) / (w₁ - v) ≤ y := (le_max_right _ _).trans hy
    rw [div_le_iff₀ (by linarith)] at h2
    nlinarith
  obtain ⟨ys, hys, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (⟨0, le_rfl, hY0⟩ : (Set.Icc 0 Y).Nonempty) hHc.continuousOn
  have hglob : ∀ y, 0 ≤ y → H y ≤ H ys := by
    intro y hy
    rcases le_total y Y with h | h
    · exact hmax ⟨hy, h⟩
    · exact (hfar y h).trans (hmax ⟨le_rfl, hY0⟩)
  -- Step 6
  refine ⟨w₁, hcw₁, hw₁w₂, ⟨ys, max ys r, hys.1, hBRex w₁ ys hys.1, ?_⟩, ?_⟩
  · intro y' q' hy' hq'
    rw [hBRuniq _ _ _ hy' hq']
    exact hglob y' hy'
  · intro y q hout q₀ hq₀
    have hq₀r : q₀ = r := (hBRuniq w₂ 0 q₀ le_rfl hq₀).trans (max_eq_right hr'.1)
    rw [hq₀r]
    have hqy : q = max y r := hBRuniq w₁ y q hout.1 hout.2.1
    obtain ⟨ε, hε, hεr, hεS⟩ := apd_Lpos μ f hD (w₂ - v) (w₁ - v) r (by linarith)
      (by linarith) hrpos
    have hHε : H 0 < H ε := by
      simp only [hH, retailerProfit, max_eq_right hεr, max_eq_right hr'.1, hS0]
      linarith
    have hge : H ε ≤ retailerProfit μ p v w₁ w₂ y q := hout.2.2 ε _ hε.le (hBRex w₁ ε hε.le)
    have hpull0 : retailerProfit μ p v w₂ w₂ 0 r = H 0 := by
      simp only [hH, retailerProfit, max_eq_right hr'.1, hS0]
      ring
    have hypos : 0 < y := by
      rcases hout.1.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h] at hqy hge
        rw [hqy] at hge
        linarith
    refine ⟨by linarith, ?_⟩
    rw [hSP, hSP, hS0]
    obtain ⟨_, hSy, _⟩ := apd_S_bounds μ y hout.1
    have hsw : s < w₁ - v := by linarith
    rcases le_or_gt y r with h | h
    · rw [hqy, max_eq_right h]
      have h1 := mul_le_mul_of_nonneg_left hSy hs0.le
      have h3 := mul_lt_mul_of_pos_right hsw hypos
      linarith
    · rw [hqy, max_eq_left h.le]
      obtain ⟨_, hSr, _⟩ := apd_S_bounds μ r hr'.1
      have h1 := mul_le_mul_of_nonneg_left hSr hs0.le
      have h2 : (w₁ - c) * r < (w₁ - c) * y := mul_lt_mul_of_pos_left h (by linarith)
      have h4 : (s - k) * r ≤ (w₁ - c) * r := mul_le_mul_of_nonneg_right (by linarith) hr'.1
      unfold apdG
      subst hk
      linarith

end CachonPushPull.ShippingCost

open CachonPushPull.ShippingCost
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (τ : ℝ) (hτ : 0 < τ) (w₂ : ℝ) (hw₂p : w₂ < p)
    (hpull : PullNoPrebook μ p c v τ w₂) :
    ∃ w₁ : ℝ, c < w₁ ∧ w₁ < w₂ ∧
      (∃ y q : ℝ, IsOutcome μ p c v τ w₁ w₂ y q) ∧
      ∀ y q : ℝ, IsOutcome μ p c v τ w₁ w₂ y q →
        ∀ q₀ : ℝ, IsSupplierBestResponse μ c v τ w₂ w₂ 0 q₀ →
          retailerProfit μ p v w₂ w₂ 0 q₀ < retailerProfit μ p v w₁ w₂ y q ∧
          supplierProfit μ c v τ w₂ w₂ 0 q₀ < supplierProfit μ c v τ w₁ w₂ y q := by
  exact apd_core μ f hD p c v hvc hcp τ hτ w₂ hw₂p hpull
