-- Prove2me | solution 1 for AvramDividend.Classical.avram_mathfin22_original_true_z_weighted_negativeband_countable_stop_mean_zero_of_clock_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:04:53.977505+00:00
-- url     : https://prove2.me/submissions/9b6a7760-56b3-4410-94a0-399549bf9e25

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_physical_negativeband_mark_quantizer_exists
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_countable_stopped_physical_signed_simple_mark_L1_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_randomclock_physical_mark_quantizer_pathwise
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_generic_centered_randomclock_compensated_integral_L1_limit
import Theorems.Thm_AvramDividend_Classical_avram_a20_bounded_Borel_mark_first_second_integral_limits
import Theorems.Thm_AvramDividend_Classical_avram_a21_finite_borel_mark_real_intensity_norm_bound_20261113
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

/-- The original physical signed z marks are centred at bounded countable random stops. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (a b : ℕ) (hab : a ≤ b)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτbound : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable)
    (hClockI : Integrable (fun ω => ((τ ω).untopA : ℝ)) P) :
    let B : Set ℝ :=
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let J : Ω → ℝ := fun ω =>
      (∫ p in Ioc 0 (τ ω).untopA ×ˢ B, p.2 ∂NX ω) -
        (((τ ω).untopA : ℝ) * (∫ z in B, z ∂X.ν))
    Integrable J P ∧ (∫ ω, J ω ∂P) = 0 := by
  classical
  intro B NX J
  let ρ : Ω → ℝ := fun ω => ((τ ω).untopA : ℝ)
  let N : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal
  obtain ⟨f, hfGlobal, hfPoint, hNIraw, _, _, _⟩ :=
    avram_mathfin22_original_physical_negativeband_mark_quantizer_exists
      X T a b hab
  let G : ℕ → Ω → ℝ := fun k ω =>
    ∫ p in Ioc 0 (τ ω).untopA ×ˢ B, f k p.2 ∂NX ω
  let c : ℕ → ℝ := fun k => ∫ z in B, f k z ∂X.ν
  let r : ℝ := ∫ z in B, z ∂X.ν
  let M : ℝ := (X.ν B).toReal
  have hNI : Integrable N P := by simpa only [N, NX, B] using hNIraw
  have hBm : MeasurableSet B := measurableSet_Ioc
  have hSep : B ⊆ Iic (-(1 / ((b : ℝ) + 1))) := fun z hz => hz.2
  have hν : X.ν B < ⊤ :=
    avram_p2_a_zero_rate_separated_borel_nu_finite X B hBm
      (1 / ((b : ℝ) + 1)) (by positivity) hSep
  have hNeg : B ⊆ Iio (0 : ℝ) := by
    intro z hz; exact lt_of_le_of_lt hz.2 (neg_lt_zero.mpr (by positivity))
  have hfBound : ∀ k z, z ∈ B → |f k z| ≤ 1 := by
    intro k z hz; simpa only [Real.norm_eq_abs] using hfGlobal k z
  have hρLe (ω : Ω) : (τ ω).untopA ≤ T := by
    have hFinite : τ ω ≠ ⊤ := by
      have hTtop : (T : WithTop ℝ≥0) < ⊤ := WithTop.coe_lt_top T
      exact ne_of_lt ((hτbound ω).trans_lt hTtop)
    exact (WithTop.untopA_le_iff hFinite).2 (hτbound ω)
  have hρBound : ∀ ω, 0 ≤ ρ ω ∧ ρ ω ≤ (T : ℝ) := by
    intro ω; exact ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.mpr (hρLe ω)⟩
  have hEach (k : ℕ) :
      Integrable (fun ω => G k ω - ρ ω * c k) P ∧
      (∫ ω, G k ω - ρ ω * c k ∂P) = 0 := by
    simpa only [G, ρ, c, B, NX] using
      (avram_mathfin22_original_countable_stopped_physical_signed_simple_mark_L1_mean_zero
        X T b B hBm hNeg hSep hν (f k) (hfBound k)
        τ hτ hτbound hτcount)
  have hGI : ∀ k, Integrable (G k) P := by
    intro k
    have hSum := (hEach k).1.add (hClockI.mul_const (c k))
    change Integrable (fun ω => G k ω - ρ ω * c k + ρ ω * c k) P at hSum
    simpa only [sub_add_cancel] using hSum
  have hPhys :=
    avram_mathfin22_original_randomclock_physical_mark_quantizer_pathwise
      X T a b hab (fun z : ℝ => z) f hfBound hfPoint
      (fun ω => (τ ω).untopA) hρLe
  have hGDom : ∀ᵐ ω ∂P, ∀ k, ‖G k ω‖ ≤ N ω := by
    apply Filter.Eventually.of_forall
    intro ω k; simpa only [G, N, NX, B, Real.norm_eq_abs] using hPhys.1 ω k
  have hGLimit : ∀ᵐ ω ∂P,
      Tendsto (fun k => G k ω) atTop
        (𝓝 (∫ p in Ioc 0 (τ ω).untopA ×ˢ B, p.2 ∂NX ω)) := by
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [G, NX, B] using hPhys.2 ω)
  have hSpatial : Tendsto c atTop (𝓝 r) := by
    simpa only [c, r] using
      (avram_a20_bounded_Borel_mark_first_second_integral_limits
        X.ν B hBm hν (fun z : ℝ => z) f hfBound hfPoint).1
  have hcBound : ∀ k, |c k| ≤ M := by
    intro k
    simpa only [c, M, Real.norm_eq_abs] using
      (avram_a21_finite_borel_mark_real_intensity_norm_bound_20261113
        X.ν B hBm hν (f k) (hfBound k))
  let R : Ω → ℝ := fun ω =>
    ∫ p in Ioc 0 (τ ω).untopA ×ˢ B, p.2 ∂NX ω
  have hSource :=
    avram_mathfin22_generic_centered_randomclock_compensated_integral_L1_limit
      G R N ρ c r M (T : ℝ) (NNReal.coe_nonneg T)
      hGI hNI hClockI hρBound hGDom hcBound
      (by simpa only [R] using hGLimit) hSpatial
      (fun k => (hEach k).2)
  simpa only [J, R, ρ, r] using hSource
