-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.mixedGaussian_surface_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:40:47.159226+00:00
-- url     : https://prove2.me/submissions/ada49f86-f0b9-4eb4-8226-809e8758087f

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_exists_mixedEmbedding_norm_lower_bound
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
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ σ ∈ normEqOneSurface K,
        ∀ a : K, a ∈ (I : Submodule (𝓞 K) K) → a ≠ 0 →
          Theta.mixedGaussian K (σ * mixedEmbedding K a) ≤ Real.exp (-Real.pi * c₀) := by
  classical
  obtain ⟨m, hm0, hm⟩ := exists_mixedEmbedding_norm_lower_bound I hI
  set d : ℝ := (finrank ℚ K : ℝ) with hd
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  refine ⟨d * (m ^ 2) ^ (d⁻¹),
    mul_pos hd0 (Real.rpow_pos_of_pos (pow_pos hm0 2) (d⁻¹)), ?_⟩
  intro σ hσ a ha ha0
  set x : mixedSpace K := σ * mixedEmbedding K a with hx
  set Q : ℝ := ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * normAtPlace w x ^ 2 with hQdef
  -- `N x = N σ · N (σ a) = N (σ a)` on the surface.
  have hnormσ : mixedEmbedding.norm σ = 1 := (mem_normEqOneSurface.mp hσ).2
  have hNx : mixedEmbedding.norm x = mixedEmbedding.norm (mixedEmbedding K a) := by
    rw [hx, map_mul, hnormσ, one_mul]
  have hNlb : m ≤ mixedEmbedding.norm x := by rw [hNx]; exact hm a ha ha0
  -- The sum of the weights is `d = [K:ℚ]`.
  have hsumw : ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) = d := by
    rw [hd, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
  -- Weighted AM-GM on the squared per-place norms.
  have hAMGM := Real.geom_mean_le_arith_mean Finset.univ
    (fun w : InfinitePlace K => (InfinitePlace.mult w : ℝ))
    (fun w : InfinitePlace K => normAtPlace w x ^ 2)
    (fun w _ => by positivity)
    (by rw [hsumw]; exact hd0)
    (fun w _ => by positivity)
  -- The geometric-mean product is `(N x)²`.
  have hprod : (∏ w : InfinitePlace K,
      (normAtPlace w x ^ 2) ^ ((InfinitePlace.mult w : ℝ)))
      = (mixedEmbedding.norm x) ^ 2 := by
    rw [mixedEmbedding.norm_apply, ← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [show ((InfinitePlace.mult w : ℝ)) = ((InfinitePlace.mult w : ℕ) : ℝ) from rfl,
      Real.rpow_natCast, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hsumw, hprod] at hAMGM
  -- `hAMGM : ((N x)²)^{1/d} ≤ Q / d`.  Bound the base below by `m²`.
  have hmono : (m ^ 2) ^ (d⁻¹) ≤ ((mixedEmbedding.norm x) ^ 2) ^ (d⁻¹) :=
    Real.rpow_le_rpow (by positivity)
      (pow_le_pow_left₀ hm0.le hNlb 2) (inv_nonneg.mpr hd0.le)
  have hge : (m ^ 2) ^ (d⁻¹) ≤ Q / d := le_trans hmono hAMGM
  have hQge : d * (m ^ 2) ^ (d⁻¹) ≤ Q := by
    rw [mul_comm]
    exact (le_div_iff₀ hd0).mp hge
  -- Conclude via monotonicity of `exp`.
  have hgauss : Theta.mixedGaussian K x = Real.exp (-Real.pi * Q) := by
    simp only [Theta.mixedGaussian, hQdef]
  rw [hgauss]
  refine Real.exp_le_exp.mpr ?_
  have hπ := Real.pi_pos
  nlinarith [hQge, hπ]
end DedekindZeta.ConeRadialReduction
