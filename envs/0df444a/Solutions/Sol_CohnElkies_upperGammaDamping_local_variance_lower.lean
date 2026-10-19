-- Prove2me | solution 1 for CohnElkies.upperGammaDamping_local_variance_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/7564de20-9860-4298-8983-7072c80da837

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaVarianceDensity_pointwise_bounds
import Theorems.Thm_CohnElkies_upperGammaVariance_bounds
import Theorems.Thm_CohnElkies_upperGammaMeasureDensity_pos
import Theorems.Thm_CohnElkies_upper_one_sub_cos_quadratic_lower
import Theorems.Thm_CohnElkies_upperGammaDampingIntegrand_integrable
import Theorems.Thm_CohnElkies_upperGammaVarianceDensity_laplace_linear_lower

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ η T : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (hT : |T| ≤ η) :
    (ℓ / (32 * Real.exp 1)) *
        upperGammaVariance ℓ η * T ^ 2 ≤
      upperGammaDamping ℓ η T := by
  let p : ℝ := 1 / (2 * η)
  let q : ℝ := 1 / η
  let C : ℝ :=
    ((ℓ / 4 + 1 / (4 * η)) * (Real.exp 1)⁻¹) *
      (T ^ 2 / 4)
  have hp : 0 < p := by
    try dsimp [p]
    positivity
  have hq : 0 < q := by
    try dsimp [q]
    positivity
  have hpq : p ≤ q := by
    try dsimp [p, q]
    calc
      1 / (2 * η) = (1 / η) / 2 := by ring
      _ ≤ 1 / η := by
        nlinarith [inv_pos.mpr hη]
  have hsubset : Ioc p q ⊆ Ioi (0 : ℝ) := by
    intro a ha
    exact hp.trans ha.1
  have hfull := upperGammaDampingIntegrand_integrable
    hℓ hη T
  have hsmall := hfull.mono_set hsubset
  have hconstant : IntegrableOn
      (fun _ : ℝ => C) (Ioc p q) := by
    exact integrableOn_const (by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hpoint : ∀ a ∈ Ioc p q,
      C ≤ upperGammaDampingIntegrand ℓ η T a := by
    intro a ha
    have ha0 : 0 < a := hp.trans ha.1
    have halower : 1 / (2 * η) ≤ a := by
      simpa [p] using! ha.1.le
    have haupper : a ≤ 1 / η := by
      simpa [q] using! ha.2
    have hquarter : 1 / (4 * η) ≤ a / 2 := by
      calc
        1 / (4 * η) = (1 / (2 * η)) / 2 := by ring
        _ ≤ a / 2 := by gcongr
    have heta : η * a ≤ 1 := by
      calc
        η * a ≤ η * (1 / η) :=
          mul_le_mul_of_nonneg_left haupper hη.le
        _ = 1 := by field_simp
    have hexp : (Real.exp 1)⁻¹ ≤
        Real.exp (-η * a) := by
      rw [← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      linarith
    have hmoment :
        (ℓ / 4 + 1 / (4 * η)) *
            (Real.exp 1)⁻¹ ≤
          a ^ 2 * upperGammaMeasureDensity ℓ η a := by
      have hbase : 0 ≤ ℓ / 4 + 1 / (4 * η) := by
        positivity
      have hgamma :=
        (upperGammaVarianceDensity_pointwise_bounds
          (η := η) hℓ ha0).1
      have hlinear :=
        upperGammaVarianceDensity_laplace_linear_lower
          (η := η) hℓ ha0
      calc
        (ℓ / 4 + 1 / (4 * η)) *
            (Real.exp 1)⁻¹ ≤
          (ℓ / 4 + 1 / (4 * η)) *
            Real.exp (-η * a) :=
          mul_le_mul_of_nonneg_left hexp hbase
        _ ≤ (ℓ / 4 + a / 2) *
            Real.exp (-η * a) := by
          gcongr
        _ ≤ a ^ 2 * upperGammaMeasureDensity ℓ η a := by
          nlinarith
    have haT : |a * T| ≤ 1 := by
      rw [abs_mul, abs_of_pos ha0]
      calc
        a * |T| ≤ a * η :=
          mul_le_mul_of_nonneg_left hT ha0.le
        _ = η * a := by ring
        _ ≤ 1 := heta
    have hcos := upper_one_sub_cos_quadratic_lower haT
    have hdensity := upperGammaMeasureDensity_pos
      (η := η) hℓ ha0
    calc
      C = (T ^ 2 / 4) *
          ((ℓ / 4 + 1 / (4 * η)) *
            (Real.exp 1)⁻¹) := by
            try dsimp [C]
            ring
      _ ≤ (T ^ 2 / 4) *
          (a ^ 2 * upperGammaMeasureDensity ℓ η a) :=
        mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ = ((a * T) ^ 2 / 4) *
          upperGammaMeasureDensity ℓ η a := by
            ring
      _ ≤ (1 - Real.cos (a * T)) *
          upperGammaMeasureDensity ℓ η a :=
        mul_le_mul_of_nonneg_right hcos hdensity.le
      _ = upperGammaDampingIntegrand ℓ η T a := rfl
  have hmono := MeasureTheory.setIntegral_mono_on
    hconstant hsmall measurableSet_Ioc hpoint
  have hnonnegative :
      0 ≤ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
        upperGammaDampingIntegrand ℓ η T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    unfold upperGammaDampingIntegrand
    exact mul_nonneg
      (sub_nonneg.mpr (Real.cos_le_one _))
      (upperGammaMeasureDensity_pos
        (η := η) hℓ ha).le
  have haesubset :
      Ioc p q ≤ᶠ[ae (volume : Measure ℝ)] Ioi 0 :=
    Filter.Eventually.of_forall
      (fun a ha => hsubset ha)
  have hrestrict := MeasureTheory.setIntegral_mono_set
    hfull hnonnegative haesubset
  have hmeasure :
      (volume : Measure ℝ).real (Ioc p q) = q - p := by
    change ((volume : Measure ℝ) (Ioc p q)).toReal = q - p
    rw [Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hpq)]
  have hconstintegral :
      (∫ a : ℝ in Ioc p q, C) = (q - p) * C := by
    rw [setIntegral_const, hmeasure]
    rfl
  have hγupper := (upperGammaVariance_bounds hℓ hη).2
  have hscaled :
      ℓ * upperGammaVariance ℓ η ≤
        ℓ / η + 1 / η ^ 2 := by
    calc
      ℓ * upperGammaVariance ℓ η ≤
          ℓ * (1 / (2 * η) + 1 / (ℓ * η ^ 2)) :=
        mul_le_mul_of_nonneg_left hγupper hℓ.le
      _ = ℓ / (2 * η) + 1 / η ^ 2 := by
        field_simp [hℓ.ne', hη.ne']
      _ ≤ ℓ / η + 1 / η ^ 2 := by
        gcongr
        linarith
  have hidentity :
      (q - p) * C =
        ((ℓ / η + 1 / η ^ 2) /
          (32 * Real.exp 1)) * T ^ 2 := by
    try dsimp [p, q, C]
    field_simp [hη.ne', (Real.exp_pos 1).ne']; ring
  calc
    (ℓ / (32 * Real.exp 1)) *
        upperGammaVariance ℓ η * T ^ 2 =
      (ℓ * upperGammaVariance ℓ η /
        (32 * Real.exp 1)) * T ^ 2 := by
          ring
    _ ≤ ((ℓ / η + 1 / η ^ 2) /
        (32 * Real.exp 1)) * T ^ 2 := by
          gcongr
    _ = (q - p) * C := hidentity.symm
    _ = ∫ a : ℝ in Ioc p q, C :=
      hconstintegral.symm
    _ ≤ ∫ a : ℝ in Ioc p q,
        upperGammaDampingIntegrand ℓ η T a := hmono
    _ ≤ ∫ a : ℝ in Ioi 0,
        upperGammaDampingIntegrand ℓ η T a := hrestrict
    _ = upperGammaDamping ℓ η T := rfl
end CohnElkies
