-- Prove2me | solution 2 for AvramDividend.Classical.bv_ac_esscher_scaled_renewal_kernel_series_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:47:33.816311+00:00
-- url     : https://prove2.me/submissions/9fbeb7ed-2692-4294-ae0e-fb703fea4d8a

import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_scaled_subunit_kernel_scale_identification
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧
      0 < ρ ∧ ρ < 1 ∧
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
      (∀ x : ℝ, 0 < x →
        IntervalIntegrable
          (fun y : ℝ => b * ∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x =
          c + ∫ y in (0 : ℝ)..x,
            (b * ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y)) := by
  obtain ⟨φ, c, ρ, b, κ, hφ, hroot, hρpos, hρlt, hbpos,
    hκcont, hκanti, hκzero, hκnonneg, hκL1, hκmass, hident⟩ :=
    bv_ac_esscher_scaled_subunit_kernel_scale_identification
      X hX q hq W hW hbv hac
  obtain ⟨hκint, F, hF0, hFsucc, _hFL1, hFnonneg, hFpoint⟩ :=
    causal_subunit_renewal_full_real_power_package
      κ ρ hρpos hρlt hκcont hκanti hκzero hκnonneg hκL1 hκmass
  have hκbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M := by
    intro ε hε
    refine ⟨κ ε, ?_⟩
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hε hx
    have hkx : 0 ≤ κ x := hκnonneg x (le_of_lt hxpos)
    have hle : κ x ≤ κ ε :=
      hκanti (mem_Ioi.mpr hε) (mem_Ioi.mpr hxpos) hx
    simpa [abs_of_nonneg hkx] using hle
  obtain ⟨hinterval, hscale⟩ := hident F hF0 hFsucc
  exact ⟨φ, c, ρ, b, κ, F, hφ, hroot, hρpos, hρlt, hκint,
    hκcont, hκzero, hκbound, hF0, hFsucc, hFnonneg, hFpoint,
    hinterval, hscale⟩
