-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_infinite_activity_continuous_full_scale_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:25:54.217955+00:00
-- url     : https://prove2.me/submissions/4232f3f0-fd06-45d2-a3b1-8425beac8d08

import Theorems.Thm_AvramDividend_Classical_bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
import Theorems.Thm_AvramDividend_Classical_bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Theorems.Thm_AvramDividend_Classical_esscher_positive_renewal_tsum_tendsto_top
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The canonical renewal-density primitive is continuous and diverges at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧ 0 < b ∧
      ContinuousOn
        (fun x : ℝ => b * ∑' n : ℕ,
          if n = 0 then (0 : ℝ) else F (n - 1) x)
        (Ioi (0 : ℝ)) ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ x : ℝ, 0 < x →
        IntervalIntegrable
          (fun y : ℝ => b * ∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x =
          c + ∫ y in (0 : ℝ)..x,
            (b * ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y)) ∧
      Tendsto (fun x : ℝ => ∑' n : ℕ, F n x)
        (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  obtain ⟨φ, c, ρ, b, κ, hκdef, hφ, hroot, hρpos, hρone,
    hbpos, hcont, hanti, hκzero, hκpos, hκL1, hmass, hrep⟩ :=
    bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
      X hX q hq W hW hbv
  obtain ⟨hκglobal, F, hFzero, hFsucc, hFL1, hFpos, hFbound⟩ :=
    causal_subunit_renewal_full_real_power_package
      κ ρ hρpos hρone hcont hanti hκzero hκpos hκL1 hmass
  obtain ⟨hFint, hFeq⟩ := hrep F hFzero hFsucc
  have hκbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M := by
    intro ε hε
    refine ⟨κ ε, ?_⟩
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hε hx
    rw [abs_of_nonneg (hκpos x (le_of_lt hxpos))]
    exact hanti hε hxpos hx
  have hshiftcont := causal_renewal_density_continuous_of_convolution_bounds
    κ F ρ hρpos hρone hκglobal hcont hκzero hκbound
    hFzero hFsucc hFpos hFbound
  have hscaled : ContinuousOn
      (fun x : ℝ => b * ∑' n : ℕ,
        if n = 0 then (0 : ℝ) else F (n - 1) x) (Ioi 0) := by
    exact hshiftcont.const_mul b
  obtain ⟨κ₂, ρ₂, hκ₂def, _, _, _, _, _, _, _, _, hκ₂div⟩ :=
    bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
      X hX hbv q hq φ hφ hroot hInfinite
  have hκeq : κ₂ = κ := by
    funext x
    rw [hκ₂def x, hκdef x]
  have hκdiv : Tendsto κ (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
    simpa only [hκeq] using hκ₂div
  have hsum : ∀ x : ℝ, 0 < x → Summable (fun n : ℕ => F n x) := by
    intro x hx
    apply renewal_density_series_summable_of_geometric_power_bound
      ρ x (le_of_lt hρpos) hρone hx (fun n : ℕ => F n x)
    · intro n
      exact hFpos n x (le_of_lt hx)
    · intro n
      exact hFbound n x hx
  have hdiv : Tendsto (fun x : ℝ => ∑' n : ℕ, F n x)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
    apply esscher_positive_renewal_tsum_tendsto_top
      κ (fun x n => F n x) hκdiv hsum
    · intro x _
      simpa only [hFzero]
    · intro x hx n
      exact hFpos n x (le_of_lt hx)
  exact ⟨φ, c, ρ, b, κ, F, hφ, hroot, hbpos, hscaled, hcont,
    hκzero, hFzero, hFsucc, hFpos, hFint, hFeq, hdiv⟩
