-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceContourDamping_secondBranch_local_coercivity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/617f0b94-48d6-4b45-a5e6-49f1325eee06

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upper_netShellVariance_bounds
import Theorems.Thm_CohnElkies_upperGammaVariance_bounds
import Theorems.Thm_CohnElkies_eventually_upperSaddleDamping_gamma_add_shell
import Theorems.Thm_CohnElkies_upperPositiveShellVariance_pos
import Theorems.Thm_CohnElkies_upperPositiveShellDamping_local_variance_lower
import Theorems.Thm_CohnElkies_upperGammaDamping_local_variance_lower

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          ∀ T : ℝ,
            |T| ≤ 1 / (2 * (shellLocation ε + 1)) →
              (ℓ / (100 * Real.exp 1)) *
                  saddleSourceGaussianVariance ε ℓ (1 + δ) *
                    T ^ 2 ≤
                saddleSourceContourDamping ε ℓ (1 + δ) T := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upperSaddleDamping_gamma_add_shell,
      eventually_upper_netShellVariance_bounds]
    with ε hε hdom hnet
  change 0 < ε at hε
  intro ℓ hℓ δ hδ T hT
  have hδnonnegative : 0 ≤ δ := by
    nlinarith
  have hη : 0 < 2 + δ := by
    linarith
  have hB : 0 ≤ shellLocation ε := by
    unfold shellLocation
    positivity
  have hhalf :
      1 / (2 * (shellLocation ε + 1)) ≤ (1 / 2 : ℝ) := by
    have hb : 0 < 2 * (shellLocation ε + 1) := by
      positivity
    apply (div_le_iff₀ hb).2
    nlinarith
  have hTgamma : |T| ≤ 2 + δ := by
    have hsmall := hT.trans hhalf
    linarith
  have hgamma := upperGammaDamping_local_variance_lower
    hℓ hη hTgamma
  have hshell := upperPositiveShellDamping_local_variance_lower
    (δ := δ) hε hℓ.le hT
  have hS : 0 ≤ upperPositiveShellVariance ε δ :=
    (upperPositiveShellVariance_pos hε hδnonnegative).le
  have hG : 0 ≤ upperGammaVariance ℓ (2 + δ) := by
    have h := (upperGammaVariance_bounds hℓ hη).1
    have hpositive : 0 < 1 / (2 * (2 + δ)) := by
      positivity
    exact hpositive.le.trans h
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hγcoefficient :
      (1 / (100 * Real.exp 1) : ℝ) ≤
        1 / (32 * Real.exp 1) := by
    gcongr
    norm_num
  have hγbase :
      0 ≤ ℓ * upperGammaVariance ℓ (2 + δ) * T ^ 2 := by
    positivity
  have hγscaled :
      (ℓ / (100 * Real.exp 1)) *
          upperGammaVariance ℓ (2 + δ) * T ^ 2 ≤
        upperGammaDamping ℓ (2 + δ) T := by
    calc
      (ℓ / (100 * Real.exp 1)) *
          upperGammaVariance ℓ (2 + δ) * T ^ 2 ≤
        (ℓ / (32 * Real.exp 1)) *
          upperGammaVariance ℓ (2 + δ) * T ^ 2 := by
            convert! mul_le_mul_of_nonneg_right
              hγcoefficient hγbase using 1 <;> ring
      _ ≤ upperGammaDamping ℓ (2 + δ) T := hgamma
  have heone : 1 ≤ Real.exp 1 :=
    (Real.one_le_exp_iff).mpr (by norm_num)
  have hscoefficient :
      (1 / (100 * Real.exp 1) : ℝ) ≤
        (99 / 100 : ℝ) * (1 / 4) := by
    calc
      (1 / (100 * Real.exp 1) : ℝ) ≤ 1 / 100 := by
        apply (div_le_iff₀ (by positivity :
          (0 : ℝ) < 100 * Real.exp 1)).2
        nlinarith
      _ ≤ (99 / 100 : ℝ) * (1 / 4) := by
        norm_num
  have hsbase :
      0 ≤ ℓ * upperPositiveShellVariance ε δ * T ^ 2 := by
    positivity
  have hsscaled :
      (ℓ / (100 * Real.exp 1)) *
          upperPositiveShellVariance ε δ * T ^ 2 ≤
        (99 / 100 : ℝ) *
          positiveShellDamping ε ℓ δ T := by
    calc
      (ℓ / (100 * Real.exp 1)) *
          upperPositiveShellVariance ε δ * T ^ 2 ≤
        (99 / 100 : ℝ) *
          ((ℓ / 4) *
            upperPositiveShellVariance ε δ * T ^ 2) := by
            convert! mul_le_mul_of_nonneg_right
              hscoefficient hsbase using 1 <;> ring
      _ ≤ (99 / 100 : ℝ) *
          positiveShellDamping ε ℓ δ T :=
        mul_le_mul_of_nonneg_left hshell (by norm_num)
  have hvariance :
      upperSaddleVariance ε ℓ δ ≤
        upperGammaVariance ℓ (2 + δ) +
          upperPositiveShellVariance ε δ := by
    unfold upperSaddleVariance
    linarith [(hnet δ hδ).2]
  have hfactor : 0 ≤
      (ℓ / (100 * Real.exp 1)) * T ^ 2 := by
    positivity
  calc
    (ℓ / (100 * Real.exp 1)) *
        saddleSourceGaussianVariance ε ℓ (1 + δ) *
          T ^ 2 =
      (ℓ / (100 * Real.exp 1)) *
        upperSaddleVariance ε ℓ δ * T ^ 2 := by
          simp [saddleSourceGaussianVariance]
    _ ≤ (ℓ / (100 * Real.exp 1)) *
          upperGammaVariance ℓ (2 + δ) * T ^ 2 +
        (ℓ / (100 * Real.exp 1)) *
          upperPositiveShellVariance ε δ * T ^ 2 := by
          convert! mul_le_mul_of_nonneg_left
            hvariance hfactor using 1 <;> ring
    _ ≤ upperGammaDamping ℓ (2 + δ) T +
        (99 / 100 : ℝ) *
          positiveShellDamping ε ℓ δ T :=
      add_le_add hγscaled hsscaled
    _ ≤ upperSaddleDamping ε ℓ δ T :=
      hdom ℓ hℓ δ hδ T
    _ = saddleSourceContourDamping ε ℓ (1 + δ) T :=
      (saddleSourceContourDamping_eq_secondBranch
        ε ℓ δ T).symm
end CohnElkies
