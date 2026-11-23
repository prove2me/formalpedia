-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.norm_idealThetaKernel_radialMap_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:40:37.04832+00:00
-- url     : https://prove2.me/submissions/3d81f6b3-88b8-41ec-a93d-32f8946716c5

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap_of_mem
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedGaussian_eq_exp_quadForm
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedGaussian_nonneg
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedQuadForm_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_summable_mixedGaussian_idealKernel
import Theorems.Thm_DedekindZeta_ConeRadialReduction_exists_pos_lower_mixedQuadForm
import Theorems.Thm_DedekindZeta_ConeRadialReduction_exists_bound_tsum_mixedGaussian_surface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply


attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) :
    ∃ c α B : ℝ, 0 < c ∧ 0 < α ∧ 0 ≤ B ∧
      ∀ r : ℝ, 1 ≤ r → ∀ σ ∈ normEqOneSurface K,
        ‖Theta.idealThetaKernel K 𝔞 (radialMap K r σ)‖ ≤ B * Real.exp (-c * r ^ α) := by
  -- The zero ideal: the kernel sums over the empty index set, hence vanishes.
  by_cases h𝔞 : 𝔞 = ⊥
  · subst h𝔞
    refine ⟨1, 1, 0, one_pos, one_pos, le_refl 0, ?_⟩
    intro r _ σ _
    have hempty : IsEmpty {a : 𝓞 K // a ∈ (⊥ : Ideal (𝓞 K)) ∧ a ≠ 0} := by
      constructor
      rintro ⟨a, ha, hne⟩
      rw [Ideal.mem_bot] at ha
      exact hne ha
    rw [Theta.idealThetaKernel, tsum_empty]
    simp
  -- Nonzero ideal. Extract the analytic constants.
  obtain ⟨q, hq, hlower⟩ := exists_pos_lower_mixedQuadForm 𝔞 h𝔞
  obtain ⟨M, hM, hMbound⟩ := exists_bound_tsum_mixedGaussian_surface 𝔞
  have hfr : 0 < (finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  set α : ℝ := 2 * (finrank ℚ K : ℝ)⁻¹ with hαdef
  have hαpos : 0 < α := by rw [hαdef]; positivity
  refine ⟨Real.pi * q, α, M * Real.exp (Real.pi * q), mul_pos Real.pi_pos hq, hαpos,
    mul_nonneg hM (Real.exp_pos _).le, ?_⟩
  intro r hr σ hσ
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  have hg_nonneg : ∀ z : mixedSpace K, 0 ≤ Theta.mixedGaussian K z := mixedGaussian_nonneg
  -- Summability of the integral-kernel Gaussian family at `radialMap K r σ` and at `σ`.
  have hxnorm : mixedEmbedding.norm (radialMap K r σ) ≠ 0 := by
    rw [norm_radialMap_of_mem r hr0 hσ]; exact hr0.ne'
  have hσnorm : mixedEmbedding.norm σ ≠ 0 := by
    rw [(mem_normEqOneSurface.mp hσ).2]; exact one_ne_zero
  have hsum_x := summable_mixedGaussian_idealKernel 𝔞 h𝔞 hxnorm
  have hsum_σ := summable_mixedGaussian_idealKernel 𝔞 h𝔞 hσnorm
  -- `‖kernel‖ ≤ ∑` of the (real, nonneg) Gaussian summands.
  have hnorm_le : ‖Theta.idealThetaKernel K 𝔞 (radialMap K r σ)‖
      ≤ ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
          Theta.mixedGaussian K (radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K)) := by
    rw [Theta.idealThetaKernel]
    have hsummablenorm : Summable (fun a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} =>
        ‖(Theta.mixedGaussian K (radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K)) : ℂ)‖) := by
      have hfun : (fun a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} =>
          ‖(Theta.mixedGaussian K (radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K)) : ℂ)‖)
          = (fun a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} => Theta.mixedGaussian K
              (radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K))) := by
        funext a
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg_nonneg _)]
      rw [hfun]; exact hsum_x
    refine (norm_tsum_le_tsum_norm hsummablenorm).trans_eq (tsum_congr (fun a => ?_))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg_nonneg _)]
  -- Per-summand radial decay split, summed up.
  have hstep : (∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
        Theta.mixedGaussian K (radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K)))
      ≤ Real.exp (-Real.pi * (r ^ α - 1) * q)
          * ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
              Theta.mixedGaussian K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun a => ?_) hsum_x
      (hsum_σ.mul_left (Real.exp (-Real.pi * (r ^ α - 1) * q)))
    have hQ : q ≤ mixedQuadForm K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) :=
      hlower σ hσ a.1 a.2.1 a.2.2
    have hmul : radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K)
        = radialMap K r (σ * mixedEmbedding K ((a : 𝓞 K) : K)) := by
      rw [radialMap, radialMap, smul_mul_assoc]
    rw [hmul, mixedGaussian_eq_exp_quadForm, mixedQuadForm_radialMap r hr0, ← hαdef,
      mixedGaussian_eq_exp_quadForm, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hprod : 0 ≤ Real.pi *
        ((r ^ α - 1) * (mixedQuadForm K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) - q)) :=
      mul_nonneg Real.pi_pos.le
        (mul_nonneg (by linarith [Real.one_le_rpow hr hαpos.le]) (by linarith))
    nlinarith [hprod]
  -- Algebra: `M · exp(-π(r^α-1)q) = (M·exp(πq)) · exp(-(πq)·r^α)`.
  have hexp_eq : Real.exp (-Real.pi * (r ^ α - 1) * q)
      = Real.exp (Real.pi * q) * Real.exp (-(Real.pi * q) * r ^ α) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ‖Theta.idealThetaKernel K 𝔞 (radialMap K r σ)‖
      ≤ ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
          Theta.mixedGaussian K (radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K)) := hnorm_le
    _ ≤ Real.exp (-Real.pi * (r ^ α - 1) * q)
          * ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
              Theta.mixedGaussian K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) := hstep
    _ ≤ Real.exp (-Real.pi * (r ^ α - 1) * q) * M :=
          mul_le_mul_of_nonneg_left (hMbound σ hσ) (Real.exp_nonneg _)
    _ = M * Real.exp (Real.pi * q) * Real.exp (-(Real.pi * q) * r ^ α) := by
          rw [hexp_eq]; ring
end DedekindZeta.ConeRadialReduction
