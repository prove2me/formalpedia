-- Prove2me | solution 1 for DedekindZeta.integrable_complexPlace_gaussian_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:22:14.545749+00:00
-- url     : https://prove2.me/submissions/9ffd3ac8-2462-4f7b-bfb5-c3706333f648

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
open MeasureTheory NumberField.mixedEmbedding
open Set
namespace DedekindZeta
theorem _root_.solution {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.Integrable
      (fun z : ℂ => Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * ‖z‖ ^ (2 * (σ - 1))) volume := by
  have hmeas : Measurable
      (fun z : ℂ => Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * ‖z‖ ^ (2 * (σ - 1))) := by
    fun_prop
  have hnonneg : 0 ≤ᵐ[volume]
      (fun z : ℂ => Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * ‖z‖ ^ (2 * (σ - 1))) := by
    filter_upwards with z
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (norm_nonneg _) _)
  have hrad : (∫⁻ x in Set.Ioi (0:ℝ),
      ENNReal.ofReal (x ^ (2*σ - 1) * Real.exp (-(2*Real.pi) * x ^ 2))) < ∞ := by
    have hb : (0:ℝ) < 2 * Real.pi := by positivity
    have hs : (-1:ℝ) < 2*σ - 1 := by linarith
    have hint := integrableOn_rpow_mul_exp_neg_mul_sq hb hs
    have hfin := hint.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal] at hfin
    · exact hfin
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (Real.exp_pos _).le
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnonneg]
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have htgt : (polarCoord.target : Set (ℝ×ℝ)) = Set.Ioi (0:ℝ) ×ˢ Ioo (-π) π := rfl
  rw [htgt]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      (g := fun p : ℝ×ℝ => ENNReal.ofReal p.1 •
        ENNReal.ofReal (Real.exp (-2 * π * p.1 ^ 2) * p.1 ^ (2 * (σ - 1)))) ?_]
  · rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
    · simp_rw [lintegral_const, Measure.restrict_apply_univ]
      rw [lintegral_mul_const]
      · refine ENNReal.mul_lt_top ?_ ?_
        · rw [setLIntegral_congr_fun measurableSet_Ioi
            (g := fun x : ℝ => ENNReal.ofReal (x ^ (2*σ-1) * Real.exp (-(2*Real.pi) * x ^ 2))) ?_]
          · exact hrad
          · intro x hx
            have hx0 : (0:ℝ) < x := hx
            dsimp only
            rw [smul_eq_mul, ← ENNReal.ofReal_mul hx0.le]
            congr 1
            rw [show (-2 * π * x ^ 2) = (-(2*π)*x^2) by ring]
            have hxc : x * x ^ (2*(σ-1)) = x ^ (2*σ-1) := by
              rw [mul_comm, ← Real.rpow_add_one (ne_of_gt hx0)]
              congr 1; ring
            rw [mul_comm (Real.exp (-(2*π)*x^2)) (x ^ (2*(σ-1))), ← mul_assoc, hxc]
        · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
      · fun_prop
    · fun_prop
  · intro p hp
    have hp1 : (0:ℝ) < p.1 := hp.1
    simp only [Complex.norm_polarCoord_symm, abs_of_pos hp1]
end DedekindZeta
