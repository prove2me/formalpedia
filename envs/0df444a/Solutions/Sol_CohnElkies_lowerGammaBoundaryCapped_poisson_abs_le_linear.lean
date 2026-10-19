-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryCapped_poisson_abs_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/41661ab6-fc85-4a05-a796-860374abf585

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripBottomMass_pos
import Theorems.Thm_CohnElkies_stripBottomMass_lt_one
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable
import Theorems.Thm_CohnElkies_integral_stripPoissonKernel
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_dimension_abs_le_linear
import Theorems.Thm_CohnElkies_harmonic_stripPoissonKernel_abs_integrable
import Theorems.Thm_CohnElkies_exists_stripPoissonKernel_uniform_abs_moment

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ σ : ℝ, -1 < σ → σ < 1 →
        ∀ s : ℝ,
          |∫ T : ℝ,
            stripPoissonKernel σ T *
              lowerGammaBoundaryCapped
                ((d : ℝ) / 2) R D
                (s - ((d : ℝ) / 2) * T)| ≤
              B * (1 + |s|) := by
  let ℓ : ℝ := (d : ℝ) / 2
  have hℓ : 0 < ℓ :=
    half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨A, hA, hdatum⟩ :=
    lowerGammaBoundaryCapped_dimension_abs_le_linear
      hd R D
  obtain ⟨M, hM, hmomentbound⟩ :=
    exists_stripPoissonKernel_uniform_abs_moment
  let B : ℝ := A * (1 + ℓ * M)
  have hB : 0 ≤ B := by
    try dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro σ hbelow habove s
  have hk := stripPoissonKernel_integrable
    hbelow habove
  have hmoment :=
    harmonic_stripPoissonKernel_abs_integrable
      hbelow habove
  have hconstant := hk.const_mul
    (A * (1 + |s|))
  have hlinear := hmoment.const_mul (A * ℓ)
  have hmajor : Integrable
      (fun T : ℝ =>
        (A * (1 + |s|)) *
            stripPoissonKernel σ T +
          (A * ℓ) *
            (stripPoissonKernel σ T * |T|)) := by
    exact hconstant.add hlinear
  have hpoint :
      ∀ᵐ T : ℝ,
        ‖stripPoissonKernel σ T *
            lowerGammaBoundaryCapped ℓ R D
              (s - ℓ * T)‖ ≤
          (A * (1 + |s|)) *
              stripPoissonKernel σ T +
            (A * ℓ) *
              (stripPoissonKernel σ T * |T|) := by
    filter_upwards [] with T
    have hkpos :=
      stripPoissonKernel_pos hbelow habove T
    have hb := hdatum (s - ℓ * T)
    have htriangle := abs_sub s (ℓ * T)
    have hmulabs : |ℓ * T| = ℓ * |T| := by
      rw [abs_mul, abs_of_pos hℓ]
    rw [hmulabs] at htriangle
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_pos hkpos, Real.norm_eq_abs]
    have hbig :
        |lowerGammaBoundaryCapped ℓ R D
          (s - ℓ * T)| ≤
          A * (1 + |s| + ℓ * |T|) := by
      calc
        |lowerGammaBoundaryCapped ℓ R D
          (s - ℓ * T)| ≤
            A * (1 + |s - ℓ * T|) := hb
        _ ≤ A * (1 + |s| + ℓ * |T|) := by
          apply mul_le_mul_of_nonneg_left _ hA
          linarith
    nlinarith [mul_nonneg hkpos.le
      (sub_nonneg.mpr hbig)]
  have hmass :=
    (stripBottomMass_lt_one hbelow).le
  have hmasspos :=
    (stripBottomMass_pos habove).le
  have hmomentle :=
    hmomentbound σ hbelow habove
  calc
    |∫ T : ℝ,
        stripPoissonKernel σ T *
          lowerGammaBoundaryCapped ℓ R D
            (s - ℓ * T)| =
      ‖∫ T : ℝ,
        stripPoissonKernel σ T *
          lowerGammaBoundaryCapped ℓ R D
            (s - ℓ * T)‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ T : ℝ,
        ((A * (1 + |s|)) *
            stripPoissonKernel σ T +
          (A * ℓ) *
            (stripPoissonKernel σ T * |T|)) :=
      norm_integral_le_of_norm_le hmajor hpoint
    _ = (A * (1 + |s|)) * stripBottomMass σ +
        (A * ℓ) *
          (∫ T : ℝ,
            stripPoissonKernel σ T * |T|) := by
      rw [integral_add hconstant hlinear,
        integral_const_mul, integral_const_mul,
        integral_stripPoissonKernel hbelow habove]
    _ ≤ A * (1 + |s|) + (A * ℓ) * M := by
      have hfirst := mul_le_mul_of_nonneg_left
        hmass (by positivity : 0 ≤ A * (1 + |s|))
      have hsecond := mul_le_mul_of_nonneg_left
        hmomentle (by positivity : 0 ≤ A * ℓ)
      nlinarith
    _ ≤ B * (1 + |s|) := by
      try dsimp [B]
      nlinarith [mul_nonneg
        (show 0 ≤ A * ℓ * M by positivity)
        (abs_nonneg s)]
end CohnElkies
