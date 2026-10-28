-- Prove2me | solution 1 for AvramDividend.Classical.excursion_resolvent_uniform_tightness_from_laplace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:39:05.705522+00:00
-- url     : https://prove2.me/submissions/e734ffb2-8de0-4bcd-8720-eccae03bbba1

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

lemma S107TI.budget
    (μ : Measure ℝ) (s R : ℝ) (hs : 0 < s)
    (hsupport : μ (Iio (0 : ℝ)) = 0)
    (δ : ENNReal)
    (hdecay : ENNReal.ofReal (Real.exp (-(s * R))) + δ ≤ 1) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂μ) +
      δ * μ (Ioi R) ≤ μ Set.univ := by
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-(s * x))) := by fun_prop
  have hind : δ * μ (Ioi R) = ∫⁻ x, (Ioi R).indicator (fun _ => δ) x ∂μ := by
    rw [lintegral_indicator_const measurableSet_Ioi]
  rw [hind, ← lintegral_add_left hmeas, ← lintegral_one]
  have hae : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]; convert hsupport using 2; ext; simp
  refine lintegral_mono_ae (hae.mono fun x hx => ?_)
  by_cases hxR : x ∈ Ioi R
  · rw [indicator_of_mem hxR]
    refine le_trans (add_le_add_left (ENNReal.ofReal_le_ofReal ?_) _) hdecay
    exact Real.exp_le_exp.2 (by have : R < x := hxR; nlinarith)
  · rw [indicator_of_notMem hxR, add_zero, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 (by nlinarith))

theorem solution (β : ℕ → Measure ℝ) (k : ℝ) (hk : 0 < k) (F : ℝ → ℝ) (hF0 : F 0 = k) (hFcont : ContinuousAt F 0) (hFpos : ∀ s : ℝ, 0 ≤ s → 0 < F s) (hmass : ∀ n : ℕ, β n univ = ENNReal.ofReal (k⁻¹)) (hsupport : ∀ n : ℕ, β n (Iio (0 : ℝ)) = 0) (hlower : ∀ n : ℕ, ∀ s : ℝ, 0 < s → ENNReal.ofReal ((F s)⁻¹) ≤ (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂β n)) : IsTightMeasureSet (Set.range β) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨η, hη0, hηε, hηlt⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hη : 0 < η := ENNReal.ofReal_pos.1 hηε
  -- choose s > 0 with k⁻¹ - (F s)⁻¹ < η / 2
  have hinv : Tendsto (fun s => (F s)⁻¹) (𝓝 (0:ℝ)) (𝓝 k⁻¹) := by
    have h := (hFcont.inv₀ (by rw [hF0]; exact hk.ne')).tendsto
    rw [Pi.inv_apply, hF0] at h; exact h
  have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), dist ((F s)⁻¹) k⁻¹ < η / 2 ∧ 0 < s :=
    ((hinv.eventually (Metric.ball_mem_nhds _ (by linarith))).filter_mono
      nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨s, hsd, hs⟩ := hev.exists
  have hsd' : k⁻¹ - (F s)⁻¹ < η / 2 := by
    rw [Real.dist_eq] at hsd; linarith [neg_abs_le ((F s)⁻¹ - k⁻¹)]
  set R : ℝ := Real.log 2 / s with hR
  have hR0 : 0 ≤ R := div_nonneg (Real.log_nonneg (by norm_num)) hs.le
  have hexp : Real.exp (-(s * R)) = 1 / 2 := by
    rw [hR, mul_div_cancel₀ _ hs.ne', Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hdecay : ENNReal.ofReal (Real.exp (-(s * R))) + ENNReal.ofReal (1 / 2) ≤ 1 := by
    rw [hexp, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
  refine ⟨Icc 0 R, isCompact_Icc, ?_⟩
  rintro μ ⟨n, rfl⟩
  have hb := S107TI.budget (β n) s R hs (hsupport n) _ hdecay
  rw [hmass n] at hb
  have hb2 := (add_le_add_left (hlower n s hs) _).trans hb
  have hFs : 0 < (F s)⁻¹ := inv_pos.2 (hFpos s hs.le)
  have hb3 : ENNReal.ofReal (1 / 2) * β n (Ioi R) ≤ ENNReal.ofReal (η / 2) := by
    have h := ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top hb2
    rw [← ENNReal.ofReal_sub _ hFs.le] at h
    exact h.trans (ENNReal.ofReal_le_ofReal hsd'.le)
  have hb4 : β n (Ioi R) ≤ ENNReal.ofReal η := by
    have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 1 := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]; norm_num
    calc β n (Ioi R) = 2 * (ENNReal.ofReal (1 / 2) * β n (Ioi R)) := by
          rw [← mul_assoc, h2, one_mul]
      _ ≤ 2 * ENNReal.ofReal (η / 2) := by gcongr
      _ = ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]; ring_nf
  have hcompl : (Icc 0 R)ᶜ ⊆ Iio 0 ∪ Ioi R := by
    intro x hx
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc β n (Icc 0 R)ᶜ ≤ β n (Iio 0 ∪ Ioi R) := measure_mono hcompl
    _ ≤ β n (Iio 0) + β n (Ioi R) := measure_union_le _ _
    _ ≤ ENNReal.ofReal η := by rw [hsupport n, zero_add]; exact hb4
    _ ≤ ε := hηlt.le
