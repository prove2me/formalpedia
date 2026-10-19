-- Prove2me | solution 1 for CohnElkies.upperFirstBranch_shortVariance_le_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/dfad3c08-c925-4c33-8222-9c332622cb83

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaVarianceDensity_integrable
import Theorems.Thm_CohnElkies_upperGammaMeasureDensity_pos
import Theorems.Thm_CohnElkies_upperFirstBranch_shortMeasure_pointwise

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a) :
    upperShortShellVariance ε (u - 1) ≤
      (1 - 4 * ε) * upperGammaVariance ℓ (1 + u) := by
  let a₀ : ℝ := shortCutoff ε
  let A : ℝ := shortEndpoint ε
  let η : ℝ := 1 + u
  let γ : ℝ → ℝ := fun a =>
    a ^ 2 * upperGammaMeasureDensity ℓ η a
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have ha₀ : 0 < a₀ := by
    try dsimp [a₀, shortCutoff]
    positivity
  have hfactor : 0 ≤ 1 - 4 * ε := by
    linarith
  have hsubset : Ioc a₀ A ⊆ Ioi (0 : ℝ) := by
    intro a ha
    exact ha₀.trans ha.1
  have hgamma : IntegrableOn γ (Ioi (0 : ℝ)) := by
    exact upperGammaVarianceDensity_integrable hℓ hη
  have hgammaOn : IntegrableOn γ (Ioc a₀ A) :=
    hgamma.mono_set hsubset
  have hscaledOn : IntegrableOn
      (fun a : ℝ => (1 - 4 * ε) * γ a)
      (Ioc a₀ A) :=
    hgammaOn.const_mul (1 - 4 * ε)
  have hs := shortShellDensity_intervalIntegrable hε horder
  have hcosh : Continuous
      (fun a : ℝ => Real.cosh (u * a)) := by
    fun_prop
  have hsquare : Continuous (fun a : ℝ => a ^ 2) := by
    fun_prop
  have hshortInterval : IntervalIntegrable
      (fun a : ℝ =>
        ℓ * (-shortShellDensity ε a) *
          Real.cosh (u * a) * a ^ 2)
      volume a₀ A := by
    have hneg : IntervalIntegrable
        (fun a : ℝ => -shortShellDensity ε a)
        volume a₀ A := by
      simpa [a₀, A, Pi.neg_apply] using! hs.neg
    exact ((hneg.const_mul ℓ).mul_continuousOn
      hcosh.continuousOn).mul_continuousOn
        hsquare.continuousOn
  have hshortOn : IntegrableOn
      (fun a : ℝ =>
        ℓ * (-shortShellDensity ε a) *
          Real.cosh (u * a) * a ^ 2)
      (Ioc a₀ A) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show a₀ ≤ A by exact horder)).mp hshortInterval
  have hpoint (a : ℝ) (ha : a ∈ Ioc a₀ A) :
      ℓ * (-shortShellDensity ε a) *
          Real.cosh (u * a) * a ^ 2 ≤
        (1 - 4 * ε) * γ a := by
    have hcomparison :=
      upperFirstBranch_shortMeasure_pointwise
        hε hεsmall hℓ (ha₀.trans ha.1)
        hulower.le huupper
        (hmargin a ⟨ha.1.le, ha.2⟩)
    have hmul :=
      mul_le_mul_of_nonneg_right hcomparison (sq_nonneg a)
    simpa [γ, η, mul_assoc, mul_left_comm, mul_comm] using! hmul
  have hmono := setIntegral_mono_on
    hshortOn hscaledOn measurableSet_Ioc hpoint
  have hnonnegative :
      0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] γ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    try dsimp [γ]
    exact mul_nonneg (sq_nonneg a)
      (upperGammaMeasureDensity_pos hℓ ha).le
  have haesubset :
      Ioc a₀ A ≤ᶠ[ae (volume : Measure ℝ)] Ioi 0 :=
    Filter.Eventually.of_forall fun a ha => hsubset ha
  have hrestrict :=
    setIntegral_mono_set hgamma hnonnegative haesubset
  have hscaleRestrict :=
    mul_le_mul_of_nonneg_left hrestrict hfactor
  have hshortEq :
      ℓ * upperShortShellVariance ε (u - 1) =
        ∫ a : ℝ in Ioc a₀ A,
          ℓ * (-shortShellDensity ε a) *
            Real.cosh (u * a) * a ^ 2 := by
    unfold upperShortShellVariance
    have hu : 1 + (u - 1) = u := by ring
    rw [hu, ← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le horder]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro a ha
    ring
  have hmain :
      ℓ * upperShortShellVariance ε (u - 1) ≤
        (1 - 4 * ε) *
          ∫ a : ℝ in Ioi 0, γ a := by
    calc
      ℓ * upperShortShellVariance ε (u - 1) =
        ∫ a : ℝ in Ioc a₀ A,
          ℓ * (-shortShellDensity ε a) *
            Real.cosh (u * a) * a ^ 2 := hshortEq
      _ ≤ ∫ a : ℝ in Ioc a₀ A,
          (1 - 4 * ε) * γ a := hmono
      _ = (1 - 4 * ε) *
          ∫ a : ℝ in Ioc a₀ A, γ a := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ (1 - 4 * ε) *
          ∫ a : ℝ in Ioi 0, γ a := hscaleRestrict
  calc
    upperShortShellVariance ε (u - 1) =
      ℓ⁻¹ * (ℓ * upperShortShellVariance ε (u - 1)) := by
        field_simp [hℓ.ne']
    _ ≤ ℓ⁻¹ *
      ((1 - 4 * ε) * ∫ a : ℝ in Ioi 0, γ a) :=
        mul_le_mul_of_nonneg_left hmain
          (inv_pos.mpr hℓ).le
    _ = (1 - 4 * ε) * upperGammaVariance ℓ (1 + u) := by
      unfold upperGammaVariance
      try dsimp [γ, η]
      ring
end CohnElkies
