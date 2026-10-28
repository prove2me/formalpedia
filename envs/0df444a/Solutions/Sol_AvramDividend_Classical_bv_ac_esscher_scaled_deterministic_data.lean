-- Prove2me | solution 1 for AvramDividend.Classical.bv_ac_esscher_scaled_deterministic_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:09:45.354726+00:00
-- url     : https://prove2.me/submissions/385acefa-a848-4c11-aa65-e6bbd5468bd1

import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_kernel_analytic_data
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The deterministic conjuncts of the corrected BV Esscher renewal-data theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ (φ ρ : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧ 0 < ρ ∧ ρ < 1 ∧
      Integrable κ volume ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M) ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 < x →
        F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) ∧
      (∀ b : ℝ, ∀ x : ℝ, 0 < x →
        IntervalIntegrable
          (fun y : ℝ => b * ∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) := by
  obtain ⟨φ, ρ, κ, hφ, hroot, hρpos, hρlt, hcont, hanti,
    hzero, hpos, hL1, hmass, hshift⟩ :=
    bv_ac_esscher_kernel_analytic_data X hX q hq hbv
  obtain ⟨hint, F, hFzero, hFrec, _hFposInt, hFpos, hFbound⟩ :=
    causal_subunit_renewal_full_real_power_package
      κ ρ hρpos hρlt hcont hanti hzero hpos hL1 hmass
  have hlocal :
      ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M := by
    intro ε hε
    refine ⟨κ ε, ?_⟩
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hε hx
    rw [abs_of_nonneg (hpos x hxpos.le)]
    exact hanti hε hxpos hx
  refine ⟨φ, ρ, κ, F, hφ, hroot, hρpos, hρlt, hint,
    hcont, hzero, hlocal, hFzero, hFrec, hFpos, hFbound, ?_⟩
  intro b x hx
  exact hshift b F hFzero hFrec x hx