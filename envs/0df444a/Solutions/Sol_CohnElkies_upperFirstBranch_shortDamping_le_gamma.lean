-- Prove2me | solution 1 for CohnElkies.upperFirstBranch_shortDamping_le_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/c4ced44b-c303-4b44-9c56-bc5d035de697

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaMeasureDensity_pos
import Theorems.Thm_CohnElkies_upperGammaDampingIntegrand_integrable
import Theorems.Thm_CohnElkies_upperFirstBranch_shortMeasure_pointwise

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (T : ℝ) :
    upperShortShellDamping ε ℓ (u - 1) T ≤
      (1 - 4 * ε) * upperGammaDamping ℓ (1 + u) T := by
  let a₀ : ℝ := shortCutoff ε
  let A : ℝ := shortEndpoint ε
  let η : ℝ := 1 + u
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
  have hgamma :=
    upperGammaDampingIntegrand_integrable hℓ hη T
  have hgammaOn : IntegrableOn
      (upperGammaDampingIntegrand ℓ η T)
      (Ioc a₀ A) :=
    hgamma.mono_set hsubset
  have hscaledOn : IntegrableOn
      (fun a : ℝ => (1 - 4 * ε) *
        upperGammaDampingIntegrand ℓ η T a)
      (Ioc a₀ A) :=
    hgammaOn.const_mul (1 - 4 * ε)
  have hs := shortShellDensity_intervalIntegrable hε horder
  have hcosh : Continuous
      (fun a : ℝ => Real.cosh (u * a)) := by
    fun_prop
  have hosc : Continuous
      (fun a : ℝ => 1 - Real.cos (a * T)) := by
    fun_prop
  have hshortInterval : IntervalIntegrable
      (fun a : ℝ =>
        ℓ * (-shortShellDensity ε a) *
          Real.cosh (u * a) *
            (1 - Real.cos (a * T)))
      volume a₀ A := by
    have hneg : IntervalIntegrable
        (fun a : ℝ => -shortShellDensity ε a)
        volume a₀ A := by
      simpa [a₀, A, Pi.neg_apply] using! hs.neg
    have hconst := hneg.const_mul ℓ
    have hwithCosh :=
      hconst.mul_continuousOn hcosh.continuousOn
    exact hwithCosh.mul_continuousOn hosc.continuousOn
  have hshortOn : IntegrableOn
      (fun a : ℝ =>
        ℓ * (-shortShellDensity ε a) *
          Real.cosh (u * a) *
            (1 - Real.cos (a * T)))
      (Ioc a₀ A) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show a₀ ≤ A by exact horder)).mp hshortInterval
  have hpoint (a : ℝ) (ha : a ∈ Ioc a₀ A) :
      ℓ * (-shortShellDensity ε a) *
          Real.cosh (u * a) *
            (1 - Real.cos (a * T)) ≤
        (1 - 4 * ε) *
          upperGammaDampingIntegrand ℓ η T a := by
    have hcomparison :=
      upperFirstBranch_shortMeasure_pointwise
        hε hεsmall hℓ (ha₀.trans ha.1)
        hulower.le huupper
        (hmargin a ⟨ha.1.le, ha.2⟩)
    have hoscNonneg : 0 ≤ 1 - Real.cos (a * T) :=
      sub_nonneg.mpr (Real.cos_le_one _)
    have hmul :=
      mul_le_mul_of_nonneg_right hcomparison hoscNonneg
    simpa [upperGammaDampingIntegrand, η, mul_assoc,
      mul_left_comm, mul_comm] using! hmul
  have hmono := setIntegral_mono_on
    hshortOn hscaledOn measurableSet_Ioc hpoint
  have hnonnegative :
      0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        upperGammaDampingIntegrand ℓ η T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    unfold upperGammaDampingIntegrand
    exact mul_nonneg
      (sub_nonneg.mpr (Real.cos_le_one _))
      (upperGammaMeasureDensity_pos hℓ ha).le
  have haesubset :
      Ioc a₀ A ≤ᶠ[ae (volume : Measure ℝ)] Ioi 0 :=
    Filter.Eventually.of_forall fun a ha => hsubset ha
  have hrestrict :=
    setIntegral_mono_set hgamma hnonnegative haesubset
  have hscaleRestrict :=
    mul_le_mul_of_nonneg_left hrestrict hfactor
  have hshortEq :
      upperShortShellDamping ε ℓ (u - 1) T =
        ∫ a : ℝ in Ioc a₀ A,
          ℓ * (-shortShellDensity ε a) *
            Real.cosh (u * a) *
              (1 - Real.cos (a * T)) := by
    unfold upperShortShellDamping
    have hu : 1 + (u - 1) = u := by ring
    rw [hu, ← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le horder]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro a ha
    ring
  calc
    upperShortShellDamping ε ℓ (u - 1) T =
        ∫ a : ℝ in Ioc a₀ A,
          ℓ * (-shortShellDensity ε a) *
            Real.cosh (u * a) *
              (1 - Real.cos (a * T)) := hshortEq
    _ ≤ ∫ a : ℝ in Ioc a₀ A,
          (1 - 4 * ε) *
            upperGammaDampingIntegrand ℓ η T a := hmono
    _ = (1 - 4 * ε) *
          ∫ a : ℝ in Ioc a₀ A,
            upperGammaDampingIntegrand ℓ η T a := by
      rw [integral_const_mul]
    _ ≤ (1 - 4 * ε) *
          ∫ a : ℝ in Ioi 0,
            upperGammaDampingIntegrand ℓ η T a :=
      hscaleRestrict
    _ = (1 - 4 * ε) *
          upperGammaDamping ℓ (1 + u) T := by
      rfl
end CohnElkies
