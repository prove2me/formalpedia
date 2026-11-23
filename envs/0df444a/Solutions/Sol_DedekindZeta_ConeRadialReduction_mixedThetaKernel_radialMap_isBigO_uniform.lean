-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.mixedThetaKernel_radialMap_isBigO_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:17.136796+00:00
-- url     : https://prove2.me/submissions/0c2940d7-f2a2-46be-958b-2f91b3dffea7

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedGaussian_surface_majorant
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedGaussian_surface_gap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedGaussian_radialMap
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
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) :
    ∃ c α B : ℝ, 0 < c ∧ 0 < α ∧ 0 ≤ B ∧
      ∀ r : ℝ, 1 ≤ r → ∀ σ ∈ normEqOneSurface K,
        ‖Theta.mixedThetaKernel K I (radialMap K r σ)‖
          ≤ B * Real.exp (-c * r ^ α) := by
  classical
  by_cases hI : I = 0
  · -- Empty index set: the kernel is the empty `tsum`, hence `0`.
    refine ⟨1, 1, 0, one_pos, one_pos, le_refl 0, ?_⟩
    intro r _hr σ _hσ
    haveI hempty : IsEmpty {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} := by
      subst hI
      refine ⟨fun a => ?_⟩
      obtain ⟨ha, ha0⟩ := a.2
      exact ha0 (by simpa using ha)
    have hzero : Theta.mixedThetaKernel K I (radialMap K r σ) = 0 := by
      rw [Theta.mixedThetaKernel,
        tsum_eq_sum (s := ∅) (fun b _ => isEmptyElim b), Finset.sum_empty]
    rw [hzero]; simp
  · -- `I ≠ 0`: combine the scaling identity, surface gap, and uniform majorant.
    obtain ⟨c₀, hc₀, hgap⟩ := mixedGaussian_surface_gap I hI
    obtain ⟨S, hS0, hSummaj⟩ := mixedGaussian_surface_majorant I hI
    have hd0 : (0:ℝ) < (finrank ℚ K : ℝ) := by
      exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
    refine ⟨Real.pi * c₀, 2 / (finrank ℚ K : ℝ), S * Real.exp (Real.pi * c₀),
      mul_pos Real.pi_pos hc₀, div_pos (by norm_num) hd0,
      mul_nonneg hS0 (Real.exp_pos _).le, ?_⟩
    intro r hr σ hσ
    have hr0 : (0:ℝ) ≤ r := le_trans zero_le_one hr
    set t : ℝ := r ^ (2 / (finrank ℚ K : ℝ)) with htdef
    have ht1 : 1 ≤ t := by
      have h := Real.rpow_le_rpow_of_exponent_le hr
        (show (0:ℝ) ≤ 2 / (finrank ℚ K : ℝ) by positivity)
      rwa [Real.rpow_zero] at h
    obtain ⟨hsum, hle⟩ := hSummaj σ hσ
    set g : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} → ℝ :=
      fun a => Theta.mixedGaussian K (σ * mixedEmbedding K (a : K)) with hgdef
    -- Per-term gap bound and positivity of the Gaussian.
    have hpos : ∀ a, 0 < g a := fun a => Real.exp_pos _
    have hgapa : ∀ a, g a ≤ Real.exp (-Real.pi * c₀) :=
      fun a => hgap σ hσ a.1 a.2.1 a.2.2
    have hElt1 : Real.exp (-Real.pi * c₀) < 1 := by
      rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
      exact Real.exp_lt_exp.mpr (by nlinarith [mul_pos Real.pi_pos hc₀])
    -- Scaling rewrite of the kernel summands (`mixedGaussian_radialMap`).
    have hker : Theta.mixedThetaKernel K I (radialMap K r σ)
        = ∑' a, ((g a ^ t : ℝ) : ℂ) := by
      rw [Theta.mixedThetaKernel]
      refine tsum_congr (fun a => ?_)
      rw [mixedGaussian_radialMap r hr0 σ (mixedEmbedding K (a : K)), ← htdef]
    -- Comparison `g^t ≤ g` (so the powered sum is summable).
    have hcmp : ∀ a, g a ^ t ≤ g a := by
      intro a
      have h1 : g a ≤ 1 := le_of_lt (lt_of_le_of_lt (hgapa a) hElt1)
      calc g a ^ t ≤ g a ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge (hpos a) h1 ht1
        _ = g a := Real.rpow_one _
    have hsumt : Summable (fun a => g a ^ t) :=
      Summable.of_nonneg_of_le (fun a => Real.rpow_nonneg (hpos a).le t) hcmp hsum
    -- Per-term majorant bound `g^t ≤ E^{t-1} · g` with `E = e^{-π c₀}`.
    have hterm : ∀ a, g a ^ t ≤ Real.exp (-Real.pi * c₀) ^ (t - 1) * g a := by
      intro a
      have e1 : g a ^ (t - 1) * g a = g a ^ t := by
        have h := Real.rpow_add (hpos a) (t - 1) 1
        rw [Real.rpow_one] at h
        rw [← h]; congr 1; ring
      have hbase : g a ^ (t - 1) ≤ Real.exp (-Real.pi * c₀) ^ (t - 1) :=
        Real.rpow_le_rpow (hpos a).le (hgapa a) (by linarith [ht1])
      calc g a ^ t = g a ^ (t - 1) * g a := e1.symm
        _ ≤ Real.exp (-Real.pi * c₀) ^ (t - 1) * g a :=
            mul_le_mul_of_nonneg_right hbase (hpos a).le
    -- Norm of each (real, nonnegative) complex summand.
    have hnormeq : ∀ a, ‖((g a ^ t : ℝ) : ℂ)‖ = g a ^ t := by
      intro a
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hpos a).le t)]
    have hsumnorm : Summable (fun a => ‖((g a ^ t : ℝ) : ℂ)‖) :=
      hsumt.congr (fun a => (hnormeq a).symm)
    -- Collapse `E^{t-1}` into a Gaussian factor.
    have hEpow : Real.exp (-Real.pi * c₀) ^ (t - 1)
        = Real.exp ((-Real.pi * c₀) * (t - 1)) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    have hfinal : Real.exp (-Real.pi * c₀) ^ (t - 1) * S
        = (S * Real.exp (Real.pi * c₀)) * Real.exp (-(Real.pi * c₀) * t) := by
      rw [hEpow, (by ring : (-Real.pi * c₀) * (t - 1)
            = Real.pi * c₀ + -(Real.pi * c₀) * t), Real.exp_add]
      ring
    calc ‖Theta.mixedThetaKernel K I (radialMap K r σ)‖
        = ‖∑' a, ((g a ^ t : ℝ) : ℂ)‖ := by rw [hker]
      _ ≤ ∑' a, ‖((g a ^ t : ℝ) : ℂ)‖ := norm_tsum_le_tsum_norm hsumnorm
      _ = ∑' a, g a ^ t := tsum_congr hnormeq
      _ ≤ ∑' a, Real.exp (-Real.pi * c₀) ^ (t - 1) * g a :=
            hsumt.tsum_le_tsum hterm (hsum.mul_left _)
      _ = Real.exp (-Real.pi * c₀) ^ (t - 1) * ∑' a, g a := tsum_mul_left
      _ ≤ Real.exp (-Real.pi * c₀) ^ (t - 1) * S :=
            mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg (Real.exp_pos _).le _)
      _ = (S * Real.exp (Real.pi * c₀)) * Real.exp (-(Real.pi * c₀) * t) := hfinal
end DedekindZeta.ConeRadialReduction
