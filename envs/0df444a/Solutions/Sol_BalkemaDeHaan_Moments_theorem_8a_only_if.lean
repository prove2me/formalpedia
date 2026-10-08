-- Prove2me | solution 1 for BalkemaDeHaan.Moments.theorem_8a_only_if
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:43:28.80377+00:00
-- url     : https://prove2.me/submissions/74cc499d-e17c-4088-a449-d8eeaa47a4b2

import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_GammaLaw
import Definitions.Def_BalkemaDeHaan_Moments_ResidualLife

open MeasureTheory Filter Topology
open MeasureTheory Filter Topology Set

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

/-- `P{X/t ≤ x | X > t} = 1 - R(xt)/R(t)` for `x ≥ 1`, `t > 0`. -/
theorem scaledResidualCDF_eq (μ : Measure ℝ) [IsFiniteMeasure μ] (t x : ℝ) (ht : 0 < t) (hx : 1 ≤ x)
    (h0 : (μ (Ioi t)).toReal ≠ 0) :
    scaledResidualCDF μ t x =
      1 - BalkemaDeHaan.LimitTypes.tail μ (x * t) / BalkemaDeHaan.LimitTypes.tail μ t := by
  unfold scaledResidualCDF BalkemaDeHaan.LimitTypes.tail
  have hsub : Ioi (x * t) ⊆ Ioi t := Ioi_subset_Ioi (by nlinarith)
  have h1 : μ (Ioc t (x * t)) = μ (Ioi t) - μ (Ioi (x * t)) := by
    rw [← Ioi_sdiff_Ioi, measure_sdiff hsub measurableSet_Ioi.nullMeasurableSet (measure_ne_top _ _)]
  rw [h1, ENNReal.toReal_sub_of_le (measure_mono hsub) (measure_ne_top _ _)]
  field_simp

/-- The tail ratio `R(xt)/R(t)` tends to `x^{-α}` for `x ≥ 1`. -/
theorem tail_ratio_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x)) (α : ℝ)
    (hlim : ∀ x : ℝ, 0 < x →
      Tendsto (fun t : ℝ => scaledResidualCDF μ t x) atTop (𝓝 (BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1))))
    (x : ℝ) (hx : 1 ≤ x) :
    Tendsto (fun t : ℝ => BalkemaDeHaan.LimitTypes.tail μ (x * t) / BalkemaDeHaan.LimitTypes.tail μ t)
      atTop (𝓝 (x ^ (-α))) := by
  have h := (hlim x (by linarith)).const_sub 1
  rw [gammaLaw_shift_eq, max_eq_left hx, sub_sub_cancel] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [scaledResidualCDF_eq μ t x ht hx (tail_pos μ hD₀ t).ne', sub_sub_cancel]

/-- Potter-type bound from a single doubling inequality for an antitone nonnegative function. -/
theorem doubling_bound (R : ℝ → ℝ) (hR : Antitone R) (hRnn : ∀ y, 0 ≤ R y) (β T : ℝ) (hT : 0 < T)
    (hβ : 0 ≤ β)
    (hdbl : ∀ t, T ≤ t → R (2 * t) ≤ 2 ^ (-β) * R t) :
    ∀ t, T ≤ t → ∀ s, 1 ≤ s → R (s * t) ≤ 2 ^ β * s ^ (-β) * R t := by
  intro t ht
  have ht0 : 0 < t := hT.trans_le ht
  have hsmall : ∀ s, 1 ≤ s → s ≤ 2 → R (s * t) ≤ 2 ^ β * s ^ (-β) * R t := by
    intro s hs1 hs2
    have h1 : R (s * t) ≤ R t := hR (by nlinarith)
    have h2 : (1:ℝ) ≤ 2 ^ β * s ^ (-β) := by
      have : (2:ℝ) ^ β * s ^ (-β) = (2 / s) ^ β := by
        rw [Real.div_rpow (by norm_num) (by linarith), Real.rpow_neg (by linarith), div_eq_mul_inv]
      rw [this]
      exact Real.one_le_rpow (by rw [le_div_iff₀ (by linarith)]; linarith) hβ
    calc R (s * t) ≤ R t := h1
      _ = 1 * R t := (one_mul _).symm
      _ ≤ 2 ^ β * s ^ (-β) * R t := mul_le_mul_of_nonneg_right h2 (hRnn t)
  have hmain : ∀ n : ℕ, ∀ s, 1 ≤ s → s ≤ 2 ^ n → R (s * t) ≤ 2 ^ β * s ^ (-β) * R t := by
    intro n
    induction n with
    | zero =>
      intro s hs1 hs2
      simp only [pow_zero] at hs2
      exact hsmall s hs1 (by linarith)
    | succ n ih =>
      intro s hs1 hs2
      by_cases h : s ≤ 2
      · exact hsmall s hs1 h
      · push_neg at h
        have hs2' : s / 2 ≤ 2 ^ n := by
          rw [div_le_iff₀ (by norm_num)]; rw [pow_succ] at hs2; linarith
        have hs1' : 1 ≤ s / 2 := by
          rw [le_div_iff₀ (by norm_num)]; linarith
        have := ih (s / 2) hs1' hs2'
        have hT' : T ≤ s / 2 * t := by nlinarith
        have h3 := hdbl (s / 2 * t) hT'
        have heq : 2 * (s / 2 * t) = s * t := by ring
        rw [heq] at h3
        calc R (s * t) ≤ 2 ^ (-β) * R (s / 2 * t) := h3
          _ ≤ 2 ^ (-β) * (2 ^ β * (s / 2) ^ (-β) * R t) :=
            mul_le_mul_of_nonneg_left this (Real.rpow_nonneg (by norm_num) _)
          _ = 2 ^ β * s ^ (-β) * R t := by
            rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
            have h4 : (2:ℝ) ^ β ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
            field_simp
  intro s hs
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt s (by norm_num : (1:ℝ) < 2)
  exact hmain n s hs hn.le


/-- Eventually, a doubling inequality with exponent `β = (ξ+α)/2` holds. -/
theorem exists_doubling (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x)) (α β : ℝ) (hβα : β < α)
    (hlim : ∀ x : ℝ, 0 < x →
      Tendsto (fun t : ℝ => scaledResidualCDF μ t x) atTop (𝓝 (BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)))) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t, T ≤ t →
      BalkemaDeHaan.LimitTypes.tail μ (2 * t) ≤ 2 ^ (-β) * BalkemaDeHaan.LimitTypes.tail μ t := by
  have h := tail_ratio_tendsto μ hD₀ α hlim 2 (by norm_num)
  have hlt : (2:ℝ) ^ (-α) < 2 ^ (-β) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hev := (h.eventually_lt_const hlt).and (eventually_ge_atTop (1:ℝ))
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  refine ⟨max T 1, le_max_right _ _, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := hT t ((le_max_left _ _).trans ht)
  rw [div_lt_iff₀ (tail_pos μ hD₀ t)] at h1
  exact h1.le

/-- A polynomial tail bound gives a finite `ξ`-th moment for `ξ < β`. -/
theorem moment_finite_of_tail_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ξ β T C : ℝ) (hξ : 0 < ξ) (hξβ : ξ < β) (hT : 0 < T)
    (hbd : ∀ y, T ≤ y → BalkemaDeHaan.LimitTypes.tail μ y ≤ C * (y / T) ^ (-β)) :
    IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ := by
  have hunion : Ioi (0:ℝ) = Ioc 0 T ∪ Ioi T := by
    ext y; simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro h; by_cases h1 : y ≤ T
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
    · rintro (h | h)
      · exact h.1
      · exact hT.trans h
  rw [hunion]
  refine IntegrableOn.union ?_ ?_
  · have hc : ContinuousOn (fun y : ℝ => y ^ ξ) (Icc 0 T) :=
      ContinuousOn.rpow_const continuousOn_id (fun y _ => Or.inr hξ.le)
    exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  · refine ⟨(measurable_id.pow_const ξ).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun y hy => Real.rpow_nonneg (hT.trans hy).le _)), tail_lintegral_identity μ ξ hξ T hT]
    refine ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _), ?_⟩
    set h : ℝ → ℝ := fun t => (C * ξ * T ^ β) * t ^ (ξ - β - 1) with hh
    have hint : IntegrableOn h (Ioi T) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hT).const_mul _
    calc ∫⁻ t in Ioi T, μ (Ioi t) * ENNReal.ofReal (ξ * t ^ (ξ - 1))
        ≤ ∫⁻ t in Ioi T, ‖h t‖ₑ := by
          apply lintegral_mono_ae
          refine ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
          have ht0 : 0 < t := hT.trans ht
          rw [← ofReal_tail, ← ENNReal.ofReal_mul (tail_nonneg μ t), ← ofReal_norm_eq_enorm]
          apply ENNReal.ofReal_le_ofReal
          refine le_trans ?_ (le_abs_self _)
          have hb := hbd t (le_of_lt ht)
          have e1 : C * (t / T) ^ (-β) * (ξ * t ^ (ξ - 1)) = h t := by
            simp only [hh]
            rw [Real.div_rpow ht0.le hT.le, Real.rpow_neg hT.le, Real.rpow_neg ht0.le]
            have : t ^ (ξ - β - 1) = t ^ (ξ - 1) * (t ^ β)⁻¹ := by
              rw [← Real.rpow_neg ht0.le, ← Real.rpow_add ht0]; ring_nf
            rw [this]
            have h1 : (t:ℝ) ^ β ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
            have h2 : (T:ℝ) ^ β ≠ 0 := (Real.rpow_pos_of_pos hT _).ne'
            field_simp
          rw [← e1]
          exact mul_le_mul_of_nonneg_right hb (mul_nonneg hξ.le (Real.rpow_nonneg ht0.le _))
      _ < ⊤ := hint.hasFiniteIntegral

/-- Change of variables: the conditional moment as an integral over `s ∈ (1, ∞)`. -/
theorem condMoment_eq_ratio_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x)) (ξ : ℝ) (hξ : 0 < ξ)
    (hmom : IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ) (t : ℝ) (ht : 0 < t) :
    condMoment μ ξ t = 1 + ξ * ∫ s in Ioi 1, s ^ (ξ - 1) *
      (BalkemaDeHaan.LimitTypes.tail μ (s * t) / BalkemaDeHaan.LimitTypes.tail μ t) := by
  obtain ⟨_, h2, h3⟩ := tail_moment_identity_core μ hD₀ ξ hξ hmom t ht
  rw [h2, h3]
  set g : ℝ → ℝ := fun y => y ^ (ξ - 1) * BalkemaDeHaan.LimitTypes.tail μ y with hg
  have htp : 0 < BalkemaDeHaan.LimitTypes.tail μ t := tail_pos μ hD₀ t
  have hcv : ∫ s in Ioi 1, s ^ (ξ - 1) *
      (BalkemaDeHaan.LimitTypes.tail μ (s * t) / BalkemaDeHaan.LimitTypes.tail μ t) =
      (t ^ (ξ - 1) * BalkemaDeHaan.LimitTypes.tail μ t)⁻¹ * ∫ s in Ioi 1, g (s * t) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hs0 : 0 < s := one_pos.trans hs
    simp only [hg]
    rw [Real.mul_rpow hs0.le ht.le]
    have h1 : (t:ℝ) ^ (ξ - 1) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
    field_simp
  rw [hcv, integral_comp_mul_right_Ioi g 1 ht, one_mul, smul_eq_mul]
  have h1 : (t:ℝ) ^ (ξ - 1) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have h2 : t ^ ξ = t ^ (ξ - 1) * t := by
    rw [Real.rpow_sub_one ht.ne']; field_simp
  rw [h2]
  field_simp
  ring

theorem ratio_integral_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (α ξ : ℝ) (hξ : 0 < ξ) (hξα : ξ < α)
    (hlim : ∀ x : ℝ, 0 < x →
      Tendsto (fun t : ℝ => scaledResidualCDF μ t x) atTop (𝓝 (BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)))) :
    Tendsto (fun t : ℝ => ∫ s in Ioi 1, s ^ (ξ - 1) *
      (BalkemaDeHaan.LimitTypes.tail μ (s * t) / BalkemaDeHaan.LimitTypes.tail μ t)) atTop
      (𝓝 (∫ s in Ioi 1, s ^ (ξ - 1 - α))) := by
  set β := (ξ + α) / 2 with hβ
  have hξβ : ξ < β := by rw [hβ]; linarith
  have hβα : β < α := by rw [hβ]; linarith
  have hβ0 : 0 ≤ β := by rw [hβ]; linarith
  obtain ⟨T, hT1, hdbl⟩ := exists_doubling μ hD₀ α β hβα hlim
  have hT : 0 < T := one_pos.trans_le hT1
  have hbd := doubling_bound (BalkemaDeHaan.LimitTypes.tail μ) (tail_antitone μ) (tail_nonneg μ)
    β T hT hβ0 hdbl
  apply tendsto_integral_filter_of_dominated_convergence (fun s => 2 ^ β * s ^ (ξ - 1 - β))
  · refine Eventually.of_forall (fun t => ?_)
    apply Measurable.aestronglyMeasurable
    exact (measurable_id.pow_const _).mul
      (((tail_measurable μ).comp (measurable_id.mul_const t)).div_const _)
  · filter_upwards [eventually_ge_atTop T] with t ht
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
    have hs0 : 0 < s := one_pos.trans hs
    have htp : 0 < BalkemaDeHaan.LimitTypes.tail μ t := tail_pos μ hD₀ t
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
      (div_nonneg (tail_nonneg μ _) (tail_nonneg μ _)))]
    have hr : BalkemaDeHaan.LimitTypes.tail μ (s * t) / BalkemaDeHaan.LimitTypes.tail μ t ≤
        2 ^ β * s ^ (-β) := by
      rw [div_le_iff₀ htp]; exact hbd t ht s (le_of_lt hs)
    calc s ^ (ξ - 1) * (BalkemaDeHaan.LimitTypes.tail μ (s * t) / BalkemaDeHaan.LimitTypes.tail μ t)
        ≤ s ^ (ξ - 1) * (2 ^ β * s ^ (-β)) :=
          mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg hs0.le _)
      _ = 2 ^ β * s ^ (ξ - 1 - β) := by
          have : s ^ (ξ - 1 - β) = s ^ (ξ - 1) * s ^ (-β) := by
            rw [← Real.rpow_add hs0]; ring_nf
          rw [this]; ring
  · exact (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
    have hs0 : 0 < s := one_pos.trans hs
    have h := (tail_ratio_tendsto μ hD₀ α hlim s (le_of_lt hs)).const_mul (s ^ (ξ - 1))
    have : s ^ (ξ - 1 - α) = s ^ (ξ - 1) * s ^ (-α) := by
      rw [← Real.rpow_add hs0]; ring_nf
    rw [this]
    exact h

theorem theorem_8a_only_if_core (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (α ξ : ℝ) (hξ : 0 < ξ) (hξα : ξ < α)
    (hlim : ∀ x : ℝ, 0 < x →
      Tendsto (fun t : ℝ => scaledResidualCDF μ t x) atTop (𝓝 (BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)))) :
    IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ ∧
    Tendsto (fun t : ℝ => condMoment μ ξ t) atTop (𝓝 (1 - ξ / α)⁻¹) := by
  have hα : 0 < α := hξ.trans hξα
  set β := (ξ + α) / 2 with hβ
  have hξβ : ξ < β := by rw [hβ]; linarith
  have hβα : β < α := by rw [hβ]; linarith
  have hβ0 : 0 ≤ β := by rw [hβ]; linarith
  obtain ⟨T, hT1, hdbl⟩ := exists_doubling μ hD₀ α β hβα hlim
  have hT : 0 < T := one_pos.trans_le hT1
  have hbd := doubling_bound (BalkemaDeHaan.LimitTypes.tail μ) (tail_antitone μ) (tail_nonneg μ)
    β T hT hβ0 hdbl
  have hmom : IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ := by
    refine moment_finite_of_tail_bound μ ξ β T (2 ^ β * BalkemaDeHaan.LimitTypes.tail μ T) hξ hξβ hT
      (fun y hy => ?_)
    have := hbd T le_rfl (y / T) (by rw [le_div_iff₀ hT]; linarith)
    rw [div_mul_cancel₀ _ hT.ne'] at this
    linarith [this]
  refine ⟨hmom, ?_⟩
  have h := ((ratio_integral_tendsto μ hD₀ α ξ hξ hξα hlim).const_mul ξ).const_add 1
  have hval : 1 + ξ * ∫ s in Ioi 1, s ^ (ξ - 1 - α) = (1 - ξ / α)⁻¹ := by
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
    have h1 : ξ - 1 - α + 1 = ξ - α := by ring
    rw [h1, one_sub_div hα.ne']
    have h3 : ξ - α ≠ 0 := by intro h; linarith
    have h4 : α - ξ ≠ 0 := by intro h; linarith
    field_simp
    ring
  rw [hval] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [condMoment_eq_ratio_integral μ hD₀ ξ hξ hmom t ht]

end BalkemaDeHaan.Moments

open BalkemaDeHaan.Moments


theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (α ξ : ℝ) (hξ : 0 < ξ) (hξα : ξ < α)
    (hlim : ∀ x : ℝ, 0 < x →
      Tendsto (fun t : ℝ => scaledResidualCDF μ t x) atTop (𝓝 (BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)))) :
    IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ ∧
    Tendsto (fun t : ℝ => condMoment μ ξ t) atTop (𝓝 (1 - ξ / α)⁻¹) := by
  exact theorem_8a_only_if_core μ hD₀ α ξ hξ hξα hlim
