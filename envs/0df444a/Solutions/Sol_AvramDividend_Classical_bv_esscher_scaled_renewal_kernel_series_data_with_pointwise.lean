-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_scaled_renewal_kernel_series_data_with_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:47:19.59545+00:00
-- url     : https://prove2.me/submissions/f5e9acda-ea6f-439f-9d49-944ba2d1940a

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ),
      (∀ t : ℝ, κ t =
        if 0 < t then
          ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
            {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
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
  classical
  obtain ⟨φ, c, ρ, b, κ, hκdef, hφ, hroot, hρpos, hρlt, hbpos,
    hκcont, hκanti, hκzero, hκpos, hκL1, hκmass, hκrep⟩ :=
    bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
      X hX q hq W hW hbv
  obtain ⟨hκInt, F, hFzero, hFsucc, _hFint, hFpos, hFbound⟩ :=
    causal_subunit_renewal_full_real_power_package
      κ ρ hρpos hρlt hκcont hκanti hκzero hκpos hκL1 hκmass
  have hκbounded : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M := by
    intro ε hε
    refine ⟨κ ε, ?_⟩
    intro x hεx
    have hxpos : 0 < x := lt_of_lt_of_le hε hεx
    have hxnonneg : 0 ≤ κ x := hκpos x (le_of_lt hxpos)
    rw [abs_of_nonneg hxnonneg]
    exact hκanti (mem_Ioi.mpr hε) (mem_Ioi.mpr hxpos) hεx
  obtain ⟨hseriesint, hscale⟩ := hκrep F hFzero hFsucc
  exact ⟨φ, c, ρ, b, κ, F, hκdef, hφ, hroot, hρpos, hρlt,
    hκInt, hκcont, hκzero, hκbounded, hFzero, hFsucc,
    hFpos, hFbound, hseriesint, hscale⟩
