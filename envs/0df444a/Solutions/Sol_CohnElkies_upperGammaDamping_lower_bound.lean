-- Prove2me | solution 1 for CohnElkies.upperGammaDamping_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/5c8be3ed-603d-4f0b-a7ba-b28a6b33a352

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaMeasureDensity_pos
import Theorems.Thm_CohnElkies_upperGammaDampingIntegrand_integrable
import Theorems.Thm_CohnElkies_upperGammaDampingIntegrand_lower_on_window

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
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    (ℓ / (8 * Real.exp 1)) *
        min (T ^ 2 / η) |T| ≤
      upperGammaDamping ℓ η T := by
  by_cases hT : T = 0
  · subst T
    simp [upperGammaDamping,
      upperGammaDampingIntegrand]
  · let q : ℝ := min η⁻¹ |T|⁻¹
    let c : ℝ :=
      (ℓ / (8 * Real.exp 1)) * T ^ 2
    have hq : 0 < q := by
      try dsimp [q]
      exact lt_min (inv_pos.mpr hη)
        (inv_pos.mpr (abs_pos.mpr hT))
    have hsubset : Ioc (0 : ℝ) q ⊆ Ioi 0 := by
      intro a ha
      exact ha.1
    have hfull :=
      upperGammaDampingIntegrand_integrable
        hℓ hη T
    have hsmall := hfull.mono_set hsubset
    have hconstant : IntegrableOn
        (fun _ : ℝ => c) (Ioc 0 q) :=
      integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top)
    have hpoint : ∀ a ∈ Ioc (0 : ℝ) q,
        c ≤ upperGammaDampingIntegrand ℓ η T a := by
      intro a ha
      apply upperGammaDampingIntegrand_lower_on_window
        hℓ hη ha.1
      · exact ha.2.trans (min_le_left _ _)
      · exact ha.2.trans (min_le_right _ _)
      · exact hT
    have hmono :=
      setIntegral_mono_on hconstant hsmall
        measurableSet_Ioc hpoint
    have hnonnegative :
        0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
          upperGammaDampingIntegrand ℓ η T := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi]
        with a ha
      unfold upperGammaDampingIntegrand
      exact mul_nonneg
        (sub_nonneg.mpr (Real.cos_le_one _))
        (upperGammaMeasureDensity_pos
          (η := η) hℓ ha).le
    have haesubset :
        Ioc (0 : ℝ) q ≤ᶠ[ae (volume : Measure ℝ)]
          Ioi 0 :=
      Filter.Eventually.of_forall fun a ha => hsubset ha
    have hrestrict :=
      setIntegral_mono_set hfull hnonnegative haesubset
    have hmeasure :
        (volume : Measure ℝ).real (Ioc (0 : ℝ) q) = q := by
      change ((volume : Measure ℝ)
        (Ioc (0 : ℝ) q)).toReal = q
      rw [Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith)]
      simp
    have hconstintegral :
        (∫ a : ℝ in Ioc (0 : ℝ) q, c) = q * c := by
      rw [setIntegral_const, hmeasure]
      rfl
    have hmin :
        q * T ^ 2 = min (T ^ 2 / η) |T| := by
      try dsimp [q]
      rw [min_mul_of_nonneg η⁻¹ |T|⁻¹
        (sq_nonneg T)]
      congr 1
      · simp [div_eq_mul_inv, mul_comm]
      · have hTabs : |T| ≠ 0 := abs_ne_zero.mpr hT
        calc
          |T|⁻¹ * T ^ 2 = |T|⁻¹ * |T| ^ 2 := by
            rw [sq_abs]
          _ = |T| := by
            field_simp [hTabs]
    calc
      (ℓ / (8 * Real.exp 1)) *
          min (T ^ 2 / η) |T| = q * c := by
        try dsimp [c]
        rw [← hmin]
        ring
      _ = ∫ a : ℝ in Ioc (0 : ℝ) q, c :=
        hconstintegral.symm
      _ ≤ ∫ a : ℝ in Ioc (0 : ℝ) q,
          upperGammaDampingIntegrand ℓ η T a :=
        hmono
      _ ≤ ∫ a : ℝ in Ioi 0,
          upperGammaDampingIntegrand ℓ η T a :=
        hrestrict
      _ = upperGammaDamping ℓ η T := rfl
end CohnElkies
