-- Prove2me | solution 1 for CohnElkies.saddleSourceMellinContour_integral_change
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/7e8475ff-342a-41ed-bb92-6a9dfc4448df

import Mathlib
import Definitions.Def_SpherePacking

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
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (u : ℝ) (F : ℂ → ℂ) :
    (∫ t : ℝ,
      F (((ℓ * (1 + u) : ℝ) : ℂ) +
        (t : ℂ) * Complex.I)) =
      (ℓ : ℂ) *
        (∫ T : ℝ,
          F (saddleSourceMellinContour ℓ u T)) := by
  let a : ℝ := ℓ * (1 + u)
  let G : ℝ → ℂ := fun t =>
    F ((a : ℂ) + (t : ℂ) * Complex.I)
  have harg (T : ℝ) :
      (a : ℂ) + (((-ℓ) * T : ℝ) : ℂ) * Complex.I =
        saddleSourceMellinContour ℓ u T := by
    try dsimp [a]
    unfold saddleSourceMellinContour
    push_cast
    ring
  have habs : |(-ℓ)⁻¹| = ℓ⁻¹ := by
    rw [inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hℓ)]
  have hchange :
      (∫ T : ℝ,
        F (saddleSourceMellinContour ℓ u T)) =
        ((ℓ⁻¹ : ℝ) : ℂ) *
          (∫ t : ℝ,
            F ((a : ℂ) + (t : ℂ) * Complex.I)) := by
    calc
      (∫ T : ℝ,
        F (saddleSourceMellinContour ℓ u T)) =
          ∫ T : ℝ, G ((-ℓ) * T) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with T
            try dsimp [G]
            rw [harg]
      _ = |(-ℓ)⁻¹| • ∫ t : ℝ, G t :=
        MeasureTheory.Measure.integral_comp_mul_left G (-ℓ)
      _ = ((ℓ⁻¹ : ℝ) : ℂ) *
          (∫ t : ℝ,
            F ((a : ℂ) + (t : ℂ) * Complex.I)) := by
          rw [habs]
          simp [G, Complex.real_smul]
  change
    (∫ t : ℝ,
      F ((a : ℂ) + (t : ℂ) * Complex.I)) =
      (ℓ : ℂ) *
        (∫ T : ℝ,
          F (saddleSourceMellinContour ℓ u T))
  rw [hchange]
  push_cast
  rw [← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast hℓ.ne'), one_mul]
end CohnElkies
