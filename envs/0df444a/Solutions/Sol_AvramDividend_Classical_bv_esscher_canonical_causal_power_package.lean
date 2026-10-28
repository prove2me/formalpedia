-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_canonical_causal_power_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:25:20.051+00:00
-- url     : https://prove2.me/submissions/f6c52219-80af-40f4-96f8-d82e533b3ef7

import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_subunit_kernel_package
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Explicit canonical Esscher renewal kernel and full real convolution powers. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ (φ : ℝ) (κ : ℝ → ℝ) (ρ : ℝ) (F : ℕ → ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧
      (∀ t : ℝ, κ t = if 0 < t then
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      Integrable κ volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 < x →
        F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) := by
  obtain ⟨φ, hφ, hroot⟩ := bv_positive_esscher_root X hX q hq hbv
  obtain ⟨κ, ρ, hκdef, hρpos, hρone, hcont, hanti,
    hκzero, hκnonneg, hκL1, hmass⟩ :=
    bv_esscher_root_positive_subunit_kernel_package
      X hX hbv q hq φ hφ hroot
  have hκpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t := by
    intro t _
    exact hκnonneg t
  obtain ⟨hκglobal, F, hFzero, hFsucc, hFL1, hFpos, hFbound⟩ :=
    causal_subunit_renewal_full_real_power_package κ ρ
      hρpos hρone hcont hanti hκzero hκpos hκL1 hmass
  exact ⟨φ, κ, ρ, F, hφ, hroot, hκdef, hρpos, hρone,
    hcont, hanti, hκzero, hκnonneg, hκglobal, hmass,
    hFzero, hFsucc, hFL1, hFpos, hFbound⟩
