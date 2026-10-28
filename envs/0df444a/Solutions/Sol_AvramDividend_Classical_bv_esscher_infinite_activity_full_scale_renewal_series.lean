-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_infinite_activity_full_scale_renewal_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:54:45.212848+00:00
-- url     : https://prove2.me/submissions/03c3b4ce-facb-41c1-bbff-83d989b8aaf0

import Theorems.Thm_AvramDividend_Classical_bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
import Theorems.Thm_AvramDividend_Classical_bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Theorems.Thm_AvramDividend_Classical_renewal_density_series_summable_of_geometric_power_bound
import Theorems.Thm_AvramDividend_Classical_esscher_positive_renewal_tsum_tendsto_top
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Infinite BV activity forces the exact scale-renewal density series to diverge at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧ 0 < b ∧
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
  obtain ⟨φ, c, ρ, b, κ, hκdef, hφ, hroot, hρpos, hρlt, hbpos,
      hκcont, hκanti, hκzero, hκpos, hκintOn, hmass, hκrepr⟩ :=
    bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
      X hX q hq W hW hbv
  obtain ⟨κ', ρ', hκ'def, _, _, _, _, _, _, _, _, htop⟩ :=
    bv_esscher_normalised_causal_kernel_diverges_of_infinite_activity
      X hX hbv q hq φ hφ hroot hInfinite
  have heq : κ = κ' := by
    funext t
    exact (hκdef t).trans (hκ'def t).symm
  have hκtop : Tendsto κ (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
    rw [heq]
    exact htop
  obtain ⟨hκint, F, hF0, hFsucc, hFint, hFpos, hFbound⟩ :=
    causal_subunit_renewal_full_real_power_package
      κ ρ hρpos hρlt hκcont hκanti hκzero hκpos hκintOn hmass
  have hsummable : ∀ x : ℝ, 0 < x → Summable (fun n : ℕ => F n x) := by
    intro x hx
    exact renewal_density_series_summable_of_geometric_power_bound
      ρ x hρpos.le hρlt hx (fun n : ℕ => F n x)
      (fun n => hFpos n x hx.le) (fun n => hFbound n x hx)
  have hfirst : ∀ x : ℝ, 0 < x → (fun n : ℕ => F n x) 0 = κ x := by
    intro x hx
    simp only [hF0]
  have hseriesnonneg : ∀ x : ℝ, 0 < x →
      ∀ n : ℕ, 0 ≤ (fun n : ℕ => F n x) n := by
    intro x hx n
    exact hFpos n x hx.le
  have hdivergence := esscher_positive_renewal_tsum_tendsto_top
    κ (fun x n => F n x) hκtop hsummable hfirst hseriesnonneg
  obtain ⟨hseriesint, hscale⟩ := hκrepr F hF0 hFsucc
  exact ⟨φ, c, ρ, b, κ, F, hφ, hroot, hbpos, hκcont,
    hκzero, hF0, hFsucc, hFpos, hseriesint, hscale, hdivergence⟩