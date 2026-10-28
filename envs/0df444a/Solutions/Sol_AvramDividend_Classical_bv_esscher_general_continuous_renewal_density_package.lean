-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_general_continuous_renewal_density_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:25:30.506993+00:00
-- url     : https://prove2.me/submissions/e84201b8-be62-40c1-978b-1c7fda450108

import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_subunit_kernel_package
import Theorems.Thm_AvramDividend_Classical_causal_subunit_shifted_renewal_density_continuous_integrable_at_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The positive Esscher root supplies a continuous origin-integrable density. -/
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
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ x : ℝ, 0 ≤ κ x) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), κ x ∂volume) = ρ ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      ContinuousOn
        (fun x : ℝ => ∑' n : ℕ,
          if n = 0 then (0 : ℝ) else F (n - 1) x)
        (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        IntervalIntegrable
          (fun y : ℝ => ∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) y)
          volume 0 x) := by
  obtain ⟨φ, hφ, hroot⟩ := bv_positive_esscher_root X hX q hq hbv
  obtain ⟨κ, ρ, hκdef, hρpos, hρone, hcont, hanti,
    hκzero, hκnonneg, hκL1, hmass⟩ :=
    bv_esscher_root_positive_subunit_kernel_package
      X hX hbv q hq φ hφ hroot
  have hκpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ κ x := by
    intro x _
    exact hκnonneg x
  obtain ⟨F, hFzero, hFsucc, hFcont, hFint⟩ :=
    causal_subunit_shifted_renewal_density_continuous_integrable_at_zero
      κ ρ 1 hρpos hρone hcont hanti hκzero hκpos hκL1 hmass
  have hFint1 : ∀ x : ℝ, 0 < x →
      IntervalIntegrable
        (fun y : ℝ => ∑' n : ℕ,
          if n = 0 then (0 : ℝ) else F (n - 1) y)
        volume 0 x := by
    intro x hx
    simpa only [one_mul] using hFint x hx
  exact ⟨φ, κ, ρ, F, hφ, hroot, hκdef, hρpos, hρone,
    hcont, hanti, hκzero, hκnonneg, hκL1, hmass,
    hFzero, hFsucc, hFcont, hFint1⟩
