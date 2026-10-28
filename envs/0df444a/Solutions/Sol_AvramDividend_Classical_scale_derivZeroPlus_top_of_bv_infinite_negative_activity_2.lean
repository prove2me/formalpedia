-- Prove2me | solution 2 for AvramDividend.Classical.scale_derivZeroPlus_top_of_bv_infinite_negative_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:40:57.941902+00:00
-- url     : https://prove2.me/submissions/32d50494-dae1-4b91-9d7a-7e4921352e92

import Theorems.Thm_AvramDividend_Classical_bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
import Theorems.Thm_AvramDividend_Classical_bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Theorems.Thm_AvramDividend_Classical_causal_renewal_shifted_tsum_eq_unshifted
import Theorems.Thm_AvramDividend_Classical_esscher_zero_right_derivative_top_of_kernel_divergence
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology intervalIntegral
open scoped NNReal ENNReal

/-- Infinite negative Lévy activity forces the bounded-variation q-scale right derivative to be infinite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    derivZeroPlus W = ⊤ := by
  classical
  obtain ⟨φ, c, ρ, b, κ, hκdef, hφ, hroot, hρpos, hρlt, hbpos,
      hκcont, hκanti, hκzero, hκpos, hκintOn, hmass, hκrepr⟩ :=
    bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
      X hX q hq W hW hBV
  obtain ⟨κ', ρ', hκ'def, _, _, _, _, _, _, _, _, htop⟩ :=
    bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
      X hX hBV q hq φ hφ hroot hInfinite
  have hκeq : κ = κ' := by
    funext t
    exact (hκdef t).trans (hκ'def t).symm
  have hκtop : Tendsto κ (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
    rw [hκeq]
    exact htop
  obtain ⟨hκint, F, hF0, hFsucc, hFint, hFpos, hFbound⟩ :=
    causal_subunit_renewal_full_real_power_package
      κ ρ hρpos hρlt hκcont hκanti hκzero hκpos hκintOn hmass
  have hκbounded : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M := by
    intro ε hε
    refine ⟨κ ε, ?_⟩
    intro x hεx
    have hxpos : 0 < x := lt_of_lt_of_le hε hεx
    have hxnonneg : 0 ≤ κ x := hκpos x hxpos.le
    rw [abs_of_nonneg hxnonneg]
    exact hκanti (mem_Ioi.mpr hε) (mem_Ioi.mpr hxpos) hεx
  have hC : ContinuousOn
      (fun x : ℝ => ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) x)
      (Ioi (0 : ℝ)) :=
    causal_renewal_density_continuous_of_convolution_bounds
      κ F ρ hρpos hρlt hκint hκcont hκzero hκbounded
      hF0 hFsucc hFpos hFbound
  let f : ℝ → ℝ := fun y =>
    b * ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y
  have hfcontOn : ContinuousOn f (Ioi (0 : ℝ)) := by
    exact hC.const_mul b
  have hfcont : ∀ x : ℝ, 0 < x → ContinuousAt f x := by
    intro x hx
    exact hfcontOn.continuousAt (isOpen_Ioi.mem_nhds hx)
  have hfmeas : ∀ x : ℝ, 0 < x →
      StronglyMeasurableAtFilter f (𝓝 x) volume := by
    exact ContinuousAt.stronglyMeasurableAtFilter
      isOpen_Ioi (fun x hx => hfcont x hx)
  obtain ⟨hfint, hscaled⟩ := hκrepr F hF0 hFsucc
  have hfint' : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x := by
    simpa only [f] using hfint
  have hscaled' : ∀ x : ℝ, 0 < x →
      Real.exp (-(φ * x)) * W x =
        c + ∫ y in (0 : ℝ)..x, f y := by
    simpa only [f] using hscaled
  have hWexpr : ∀ x : ℝ, 0 < x →
      W x = Real.exp (φ * x) * (c + ∫ y in (0 : ℝ)..x, f y) := by
    intro x hx
    have he : Real.exp (φ * x) * Real.exp (-(φ * x)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      W x = (Real.exp (φ * x) * Real.exp (-(φ * x))) * W x := by
        rw [he, one_mul]
      _ = Real.exp (φ * x) * (Real.exp (-(φ * x)) * W x) := by
        rw [mul_assoc]
      _ = Real.exp (φ * x) * (c + ∫ y in (0 : ℝ)..x, f y) := by
        rw [hscaled' x hx]
  have hbracket : ∀ x : ℝ, 0 < x →
      0 ≤ c + ∫ y in (0 : ℝ)..x, f y := by
    intro x hx
    calc
      0 ≤ Real.exp (-(φ * x)) * W x :=
        mul_nonneg (Real.exp_nonneg _) (hW.2.1 x hx.le)
      _ = c + ∫ y in (0 : ℝ)..x, f y := hscaled' x hx
  have hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x := by
    intro x hx
    have hs : 0 ≤ ∑' n : ℕ,
        if n = 0 then (0 : ℝ) else F (n - 1) x := by
      apply tsum_nonneg
      intro n
      cases n with
      | zero => simp
      | succ n => simpa using hFpos n x hx.le
    exact mul_nonneg hbpos.le hs
  have hsummable : ∀ x : ℝ, 0 < x → Summable (fun n : ℕ => F n x) := by
    intro x hx
    exact renewal_density_series_summable_of_geometric_power_bound
      ρ x hρpos.le hρlt hx (fun n : ℕ => F n x)
      (fun n => hFpos n x hx.le) (fun n => hFbound n x hx)
  have hfirst_le : ∀ x : ℝ, 0 < x →
      κ x ≤ ∑' n : ℕ, F n x := by
    intro x hx
    have hsum_le := sum_le_hasSum ({0} : Finset ℕ)
      (by intro n hn; exact hFpos n x hx.le)
      (hsummable x hx).hasSum
    simpa only [Finset.sum_singleton, hF0] using hsum_le
  have hk : ∀ x : ℝ, 0 < x → b * κ x ≤ f x := by
    intro x hx
    have hshift := causal_renewal_shifted_tsum_eq_unshifted
      (fun n : ℕ => F n x) (hsummable x hx)
    change b * κ x ≤ b * ∑' n : ℕ,
      if n = 0 then (0 : ℝ) else F (n - 1) x
    rw [hshift]
    exact mul_le_mul_of_nonneg_left (hfirst_le x hx) hbpos.le
  have htop' : Tendsto (fun x : ℝ => b * κ x)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop :=
    Filter.Tendsto.const_mul_atTop hbpos hκtop
  exact esscher_zero_right_derivative_top_of_kernel_divergence
    W φ c f (fun x => b * κ x) hφ.le hWexpr hfint'
    hfmeas hfcont hbracket hfnonneg hk htop'