-- Prove2me | solution 1 for BalkemaDeHaan.Moments.gamma_moment
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:37:33.685056+00:00
-- url     : https://prove2.me/submissions/d2b20f8e-d97a-46ab-a4b0-1992cedb7434

import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_GammaLaw
import Definitions.Def_BalkemaDeHaan_Moments_ResidualLife

open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter Topology Set

namespace BalkemaDeHaan.Moments

/-- Layer-cake identity: `∫_{(x,∞)} y^ξ dμ = x^ξ μ(x,∞) + ∫_x^∞ ξ t^{ξ-1} μ(t,∞) dt` in `ℝ≥0∞`. -/
theorem tail_lintegral_identity (μ : Measure ℝ) (ξ : ℝ) (hξ : 0 < ξ) (x : ℝ) (hx : 0 < x) :
    ∫⁻ y in Ioi x, ENNReal.ofReal (y ^ ξ) ∂μ =
      ENNReal.ofReal (x ^ ξ) * μ (Ioi x) +
        ∫⁻ t in Ioi x, μ (Ioi t) * ENNReal.ofReal (ξ * t ^ (ξ - 1)) := by
  set g : ℝ → ℝ := fun t => if x < t then ξ * t ^ (ξ - 1) else 0 with hg
  have hgind : g = (Ioi x).indicator (fun t => ξ * t ^ (ξ - 1)) := by
    ext t; simp [hg, Set.indicator, Set.mem_Ioi]
  have g_intble : ∀ T > 0, IntervalIntegrable g volume 0 T := by
    intro T hT
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le, hgind, IntegrableOn,
      integrable_indicator_iff measurableSet_Ioi, IntegrableOn, Measure.restrict_restrict measurableSet_Ioi]
    have hcont : ContinuousOn (fun t : ℝ => ξ * t ^ (ξ - 1)) (Icc x T) := by
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.rpow_const continuousOn_id
      intro t ht; left; exact (hx.trans_le ht.1).ne'
    exact (hcont.integrableOn_Icc).mono_set (fun t ht => ⟨ht.1.le, ht.2.2⟩)
  have g_nn : ∀ t, 0 ≤ g t := by
    intro t; simp only [hg]
    split_ifs with h
    · exact mul_nonneg hξ.le (Real.rpow_nonneg (hx.trans h).le _)
    · exact le_rfl
  have key := lintegral_comp_eq_lintegral_meas_lt_mul (μ.restrict (Ioi x)) (f := id)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => (hx.trans hy).le))
    measurable_id.aemeasurable g_intble (Eventually.of_forall g_nn)
  -- evaluate the inner interval integral
  have hinner : ∀ y, x < y → ∫ t in (0:ℝ)..y, g t = y ^ ξ - x ^ ξ := by
    intro y hy
    have h1 : IntervalIntegrable g volume 0 x := g_intble x hx
    have h2 : IntervalIntegrable g volume x y :=
      (g_intble y (hx.trans hy)).mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le (hx.trans hy).le]; exact ⟨hx.le, hy.le⟩) right_mem_uIcc)
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    have h3 : ∫ t in (0:ℝ)..x, g t = 0 := by
      apply intervalIntegral.integral_zero_ae
      refine Eventually.of_forall (fun t ht => ?_)
      rw [uIoc_of_le hx.le] at ht
      simp [hg, not_lt.mpr ht.2]
    have h4 : ∫ t in x..y, g t = ∫ t in x..y, ξ * t ^ (ξ - 1) := by
      apply intervalIntegral.integral_congr_ae
      refine Eventually.of_forall (fun t ht => ?_)
      rw [uIoc_of_le hy.le] at ht
      simp [hg, ht.1]
    rw [h3, h4, intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by intro h; linarith,
      notMem_uIcc_of_lt hx (hx.trans hy)⟩)]
    rw [sub_add_cancel]; field_simp; ring
  have hL : ∫⁻ y, ENNReal.ofReal (∫ t in (0:ℝ)..id y, g t) ∂(μ.restrict (Ioi x)) =
      ∫⁻ y in Ioi x, ENNReal.ofReal (y ^ ξ - x ^ ξ) ∂μ := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy; simp only [id]; rw [hinner y hy]
  have hR : ∫⁻ t in Ioi 0, (μ.restrict (Ioi x)) {a : ℝ | t < id a} * ENNReal.ofReal (g t) =
      ∫⁻ t in Ioi x, μ (Ioi t) * ENNReal.ofReal (ξ * t ^ (ξ - 1)) := by
    have : ∀ t ∈ Ioi (0:ℝ), (μ.restrict (Ioi x)) {a : ℝ | t < id a} * ENNReal.ofReal (g t) =
        (Ioi x).indicator (fun t => μ (Ioi t) * ENNReal.ofReal (ξ * t ^ (ξ - 1))) t := by
      intro t ht
      simp only [id, hg, Set.indicator, mem_Ioi]
      split_ifs with h
      · congr 1
        rw [Measure.restrict_apply' measurableSet_Ioi]
        have : ({a : ℝ | t < a} ∩ Ioi x) = Ioi t :=
          inter_eq_left.mpr (fun a (ha : t < a) => h.trans ha)
        rw [this]
      · simp
    rw [setLIntegral_congr_fun measurableSet_Ioi this, lintegral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr (Ioi_subset_Ioi hx.le)]
  rw [hL, hR] at key
  rw [← key, ← setLIntegral_const, ← lintegral_add_left measurable_const]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro y hy
  show ENNReal.ofReal (y ^ ξ) = ENNReal.ofReal (x ^ ξ) + ENNReal.ofReal (y ^ ξ - x ^ ξ)
  rw [← ENNReal.ofReal_add (Real.rpow_nonneg hx.le _)
    (sub_nonneg.mpr (Real.rpow_le_rpow hx.le (le_of_lt hy) hξ.le))]
  congr 1; ring


theorem tail_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] : Antitone (BalkemaDeHaan.LimitTypes.tail μ) := by
  intro a b hab
  unfold BalkemaDeHaan.LimitTypes.tail
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Ioi_subset_Ioi hab))

theorem tail_measurable (μ : Measure ℝ) [IsFiniteMeasure μ] : Measurable (BalkemaDeHaan.LimitTypes.tail μ) :=
  (tail_antitone μ).measurable

theorem tail_nonneg (μ : Measure ℝ) (y : ℝ) : 0 ≤ BalkemaDeHaan.LimitTypes.tail μ y :=
  ENNReal.toReal_nonneg

theorem ofReal_tail (μ : Measure ℝ) [IsFiniteMeasure μ] (y : ℝ) :
    ENNReal.ofReal (BalkemaDeHaan.LimitTypes.tail μ y) = μ (Ioi y) :=
  ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- Real-valued form of the layer cake identity, given a finite `ξ`-th moment. -/
theorem tail_integral_identity (μ : Measure ℝ) [IsFiniteMeasure μ]
    (ξ : ℝ) (hξ : 0 < ξ)
    (hmom : IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ)
    (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun y : ℝ => y ^ (ξ - 1) * BalkemaDeHaan.LimitTypes.tail μ y) (Set.Ioi x) ∧
    (∫ y in Set.Ioi x, y ^ ξ ∂μ) =
      x ^ ξ * BalkemaDeHaan.LimitTypes.tail μ x +
        ξ * (∫ y in Set.Ioi x, y ^ (ξ - 1) * BalkemaDeHaan.LimitTypes.tail μ y) := by
  have key := tail_lintegral_identity μ ξ hξ x hx
  have hmom' : IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi x) μ := hmom.mono_set (Ioi_subset_Ioi hx.le)
  have hnn : 0 ≤ᵐ[μ.restrict (Ioi x)] (fun y : ℝ => y ^ ξ) :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => Real.rpow_nonneg (hx.trans hy).le _)
  rw [← ofReal_integral_eq_lintegral_ofReal hmom' hnn] at key
  set F : ℝ → ℝ := fun t => t ^ (ξ - 1) * BalkemaDeHaan.LimitTypes.tail μ t with hF
  have hFmeas : Measurable F := (measurable_id.pow_const _).mul (tail_measurable μ)
  have hFnn : ∀ t ∈ Ioi x, 0 ≤ F t := fun t ht =>
    mul_nonneg (Real.rpow_nonneg (hx.trans ht).le _) (tail_nonneg μ t)
  have hR : ∫⁻ t in Ioi x, μ (Ioi t) * ENNReal.ofReal (ξ * t ^ (ξ - 1)) =
      ∫⁻ t in Ioi x, ENNReal.ofReal (ξ * F t) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    show μ (Ioi t) * ENNReal.ofReal (ξ * t ^ (ξ - 1)) = ENNReal.ofReal (ξ * F t)
    rw [← ofReal_tail, ← ENNReal.ofReal_mul (tail_nonneg μ t)]
    congr 1; simp only [hF]; ring
  rw [hR] at key
  have hfin : ∫⁻ t in Ioi x, ENNReal.ofReal (ξ * F t) < ⊤ := by
    have : ENNReal.ofReal (∫ y in Set.Ioi x, y ^ ξ ∂μ) < ⊤ := ENNReal.ofReal_lt_top
    rw [key] at this
    exact (ENNReal.add_lt_top.mp this).2
  have hint : IntegrableOn (fun t => ξ * F t) (Ioi x) := by
    refine ⟨(hFmeas.const_mul ξ).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => mul_nonneg hξ.le (hFnn t ht)))]
    exact hfin
  have hintF : IntegrableOn F (Ioi x) := by
    have := hint.const_mul ξ⁻¹
    refine (IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi)
    field_simp
  refine ⟨hintF, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => mul_nonneg hξ.le (hFnn t ht))), ← ofReal_tail,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _), ← ENNReal.ofReal_add
      (mul_nonneg (Real.rpow_nonneg hx.le _) (tail_nonneg μ x))
      (integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioi
        (fun t ht => mul_nonneg hξ.le (hFnn t ht))))] at key
  rw [ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hnn)
    (add_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (tail_nonneg μ x))
      (integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioi
        (fun t ht => mul_nonneg hξ.le (hFnn t ht)))))] at key
  rw [key, integral_const_mul]

theorem tail_pos (μ : Measure ℝ) [IsFiniteMeasure μ] (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x)) (x : ℝ) :
    0 < BalkemaDeHaan.LimitTypes.tail μ x :=
  ENNReal.toReal_pos (hD₀ x).ne' (measure_ne_top _ _)

theorem condMoment_eq (μ : Measure ℝ) (ξ : ℝ) (x : ℝ) (hx : 0 < x) :
    condMoment μ ξ x = (∫ y in Set.Ioi x, y ^ ξ ∂μ) / (x ^ ξ * BalkemaDeHaan.LimitTypes.tail μ x) := by
  unfold condMoment BalkemaDeHaan.LimitTypes.tail
  have : (∫ y in Ioi x, (y / x) ^ ξ ∂μ) = (∫ y in Ioi x, y ^ ξ ∂μ) / x ^ ξ := by
    rw [← integral_div]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    exact Real.div_rpow (hx.trans hy).le hx.le ξ
  rw [this, div_div]

theorem tail_moment_identity_core (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (ξ : ℝ) (hξ : 0 < ξ)
    (hmom : IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ)
    (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun y : ℝ => y ^ (ξ - 1) * BalkemaDeHaan.LimitTypes.tail μ y) (Set.Ioi x) ∧
    condMoment μ ξ x = (∫ y in Set.Ioi x, y ^ ξ ∂μ) / (x ^ ξ * BalkemaDeHaan.LimitTypes.tail μ x) ∧
    (∫ y in Set.Ioi x, y ^ ξ ∂μ) / (x ^ ξ * BalkemaDeHaan.LimitTypes.tail μ x) =
      ξ * (∫ y in Set.Ioi x, y ^ (ξ - 1) * BalkemaDeHaan.LimitTypes.tail μ y) / (x ^ ξ * BalkemaDeHaan.LimitTypes.tail μ x) + 1 := by
  obtain ⟨h1, h2⟩ := tail_integral_identity μ ξ hξ hmom x hx
  refine ⟨h1, condMoment_eq μ ξ x hx, ?_⟩
  have hpos : 0 < x ^ ξ * BalkemaDeHaan.LimitTypes.tail μ x :=
    mul_pos (Real.rpow_pos_of_pos hx _) (tail_pos μ hD₀ x)
  have ht : BalkemaDeHaan.LimitTypes.tail μ x ≠ 0 := (tail_pos μ hD₀ x).ne'
  have hx' : x ^ ξ ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  rw [h2]; field_simp; ring


theorem gammaLaw_shift_eq (α x : ℝ) :
    BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1) = 1 - (max x 1) ^ (-α) := by
  unfold BalkemaDeHaan.ParetoBounds.GammaLaw
  split_ifs with h
  · rw [max_eq_left (by linarith)]; ring_nf
  · rw [max_eq_right (by linarith)]; simp

theorem paretoG_continuous (α : ℝ) : Continuous (fun x : ℝ => 1 - (max x 1) ^ (-α)) := by
  apply continuous_const.sub
  apply Continuous.rpow_const (continuous_id.max continuous_const)
  intro x; left; exact (lt_of_lt_of_le one_pos (le_max_right x 1)).ne'

theorem paretoG_monotone (α : ℝ) (hα : 0 < α) : Monotone (fun x : ℝ => 1 - (max x 1) ^ (-α)) := by
  intro a b hab
  simp only
  have h1 : (0:ℝ) < max a 1 := lt_of_lt_of_le one_pos (le_max_right a 1)
  have h2 : (0:ℝ) < max b 1 := lt_of_lt_of_le one_pos (le_max_right b 1)
  have := Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (r := -α) (by linarith) h1 h2
    (max_le_max_right 1 hab)
  linarith

theorem paretoG_tendsto_atBot (α : ℝ) : Tendsto (fun x : ℝ => 1 - (max x 1) ^ (-α)) atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_le_atBot (1:ℝ)] with x hx
  rw [max_eq_right hx, Real.one_rpow]; ring

theorem paretoG_tendsto_atTop (α : ℝ) (hα : 0 < α) :
    Tendsto (fun x : ℝ => 1 - (max x 1) ^ (-α)) atTop (𝓝 1) := by
  have h := (tendsto_rpow_neg_atTop hα).const_sub 1
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  rw [max_eq_left hx]

/-- The Pareto-type law with cdf `x ↦ Γ_α(x-1)`. -/
noncomputable def paretoSF (α : ℝ) (hα : 0 < α) : StieltjesFunction ℝ where
  toFun := fun x : ℝ => 1 - (max x 1) ^ (-α)
  mono' := paretoG_monotone α hα
  right_continuous' := fun x => (paretoG_continuous α).continuousAt.continuousWithinAt

theorem gamma_law_exists (α : ℝ) (hα : 0 < α) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ∀ x : ℝ, cdf ν x = BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1) := by
  refine ⟨(paretoSF α hα).measure,
    (paretoSF α hα).isProbabilityMeasure (paretoG_tendsto_atBot α) (paretoG_tendsto_atTop α hα), ?_⟩
  intro x
  rw [cdf_measure_stieltjesFunction _ (paretoG_tendsto_atBot α) (paretoG_tendsto_atTop α hα),
    gammaLaw_shift_eq]
  rfl

theorem gamma_law_tail (α : ℝ) (hα : 0 < α) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ x : ℝ, cdf ν x = BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)) (t : ℝ) :
    ν (Ioi t) = ENNReal.ofReal ((max t 1) ^ (-α)) := by
  have hm : (max t 1) ^ (-α) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (le_max_right t 1) (by linarith)
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
    ← ofReal_cdf, hν, gammaLaw_shift_eq, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (by linarith)]
  congr 1; ring

theorem gamma_law_Ioc_zero (α : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ x : ℝ, cdf ν x = BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)) :
    ν (Ioc 0 1) = 0 := by
  apply le_antisymm _ zero_le
  calc ν (Ioc 0 1) ≤ ν (Iic 1) := measure_mono Ioc_subset_Iic_self
    _ = 0 := by rw [← ofReal_cdf, hν, gammaLaw_shift_eq]; simp

theorem gamma_law_lintegral (α ξ : ℝ) (hξ : 0 < ξ) (hξα : ξ < α)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ x : ℝ, cdf ν x = BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)) :
    ∫⁻ y in Ioi 1, ENNReal.ofReal (y ^ ξ) ∂ν = ENNReal.ofReal ((1 - ξ / α)⁻¹) := by
  have hα : 0 < α := hξ.trans hξα
  rw [tail_lintegral_identity ν ξ hξ 1 one_pos, Real.one_rpow, ENNReal.ofReal_one, one_mul,
    gamma_law_tail α hα ν hν 1, max_self, Real.one_rpow, ENNReal.ofReal_one]
  have hR : ∫⁻ t in Ioi 1, ν (Ioi t) * ENNReal.ofReal (ξ * t ^ (ξ - 1)) =
      ∫⁻ t in Ioi 1, ENNReal.ofReal (ξ * t ^ (ξ - α - 1)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    show ν (Ioi t) * ENNReal.ofReal (ξ * t ^ (ξ - 1)) = ENNReal.ofReal (ξ * t ^ (ξ - α - 1))
    rw [gamma_law_tail α hα ν hν t, max_eq_left (le_of_lt ht), ← ENNReal.ofReal_mul
      (Real.rpow_nonneg (by linarith [ht.out]) _)]
    congr 1
    have : t ^ (ξ - α - 1) = t ^ (-α) * t ^ (ξ - 1) := by
      rw [← Real.rpow_add (by linarith [ht.out])]; ring_nf
    rw [this]; ring
  rw [hR]
  have hint : IntegrableOn (fun t : ℝ => ξ * t ^ (ξ - α - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul ξ
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => mul_nonneg hξ.le (Real.rpow_nonneg (by linarith [ht.out]) _))),
    integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one]
  · congr 1
    have h1 : ξ - α - 1 + 1 = ξ - α := by ring
    have h3 : ξ - α ≠ 0 := by intro h; linarith
    have h4 : α - ξ ≠ 0 := by intro h; linarith
    rw [h1, one_sub_div hα.ne']
    field_simp
    ring
  · apply mul_nonneg hξ.le
    have h1 : ξ - α - 1 + 1 = ξ - α := by ring
    rw [h1]
    exact div_nonneg_iff.mpr (Or.inr ⟨by norm_num, by linarith⟩)

theorem gamma_moment_core (α ξ : ℝ) (hξ : 0 < ξ) (hξα : ξ < α) :
    (∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ x : ℝ, cdf ν x = BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)) ∧
    ∀ ν : Measure ℝ, IsProbabilityMeasure ν → (∀ x : ℝ, cdf ν x = BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)) →
      IntegrableOn (fun x : ℝ => x ^ ξ) (Set.Ioi 0) ν ∧
      ∫ x in Set.Ioi 0, x ^ ξ ∂ν = (1 - ξ / α)⁻¹ := by
  have hα : 0 < α := hξ.trans hξα
  refine ⟨gamma_law_exists α hα, ?_⟩
  intro ν hprob hν
  have hL := gamma_law_lintegral α ξ hξ hξα ν hν
  have hnn1 : 0 ≤ᵐ[ν.restrict (Ioi 1)] (fun y : ℝ => y ^ ξ) :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => Real.rpow_nonneg (by linarith [hy.out]) _)
  have hmeas : AEStronglyMeasurable (fun y : ℝ => y ^ ξ) (ν.restrict (Ioi 1)) :=
    (measurable_id.pow_const ξ).aestronglyMeasurable
  have hint1 : IntegrableOn (fun y : ℝ => y ^ ξ) (Ioi 1) ν := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn1, hL]
    exact ENNReal.ofReal_lt_top
  have hint0 : IntegrableOn (fun y : ℝ => y ^ ξ) (Ioc 0 1) ν := by
    rw [IntegrableOn, Measure.restrict_eq_zero.mpr (gamma_law_Ioc_zero α ν hν)]
    exact integrable_zero_measure
  have hunion : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext y; simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro h; by_cases h1 : y ≤ 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
    · rintro (h | h)
      · exact h.1
      · exact lt_trans one_pos h
  rw [hunion]
  refine ⟨hint0.union hint1, ?_⟩
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint0 hint1,
    Measure.restrict_eq_zero.mpr (gamma_law_Ioc_zero α ν hν), integral_zero_measure, zero_add,
    integral_eq_lintegral_of_nonneg_ae hnn1 hmeas, hL, ENNReal.toReal_ofReal]
  have h2 : 0 < 1 - ξ / α := by
    rw [sub_pos, div_lt_one hα]; exact hξα
  exact (inv_pos.mpr h2).le

end BalkemaDeHaan.Moments

open BalkemaDeHaan.Moments


theorem solution (α ξ : ℝ) (hξ : 0 < ξ) (hξα : ξ < α) :
    (∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ x : ℝ, cdf ν x = BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)) ∧
    ∀ ν : Measure ℝ, IsProbabilityMeasure ν → (∀ x : ℝ, cdf ν x = BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)) →
      IntegrableOn (fun x : ℝ => x ^ ξ) (Set.Ioi 0) ν ∧
      ∫ x in Set.Ioi 0, x ^ ξ ∂ν = (1 - ξ / α)⁻¹ := by
  exact gamma_moment_core α ξ hξ hξα
