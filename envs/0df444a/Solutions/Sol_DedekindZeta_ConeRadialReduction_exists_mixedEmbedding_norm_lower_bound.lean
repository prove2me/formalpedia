-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.exists_mixedEmbedding_norm_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:37:46.543457+00:00
-- url     : https://prove2.me/submissions/9f7ba1a1-757a-412c-9353-48afe2500d56

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
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
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K)
    (hI : I ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ a : K, a ∈ (I : Submodule (𝓞 K) K) → a ≠ 0 →
      m ≤ mixedEmbedding.norm (mixedEmbedding K a) := by
  classical
  -- A nonzero algebraic integer has `mixedEmbedding.norm ≥ 1`.
  have hint_ge : ∀ c : 𝓞 K, c ≠ 0 →
      (1 : ℝ) ≤ mixedEmbedding.norm (mixedEmbedding K ((c : 𝓞 K) : K)) := by
    intro c hc
    rw [mixedEmbedding.norm_eq_norm, ← Algebra.coe_norm_int]
    have hz : Algebra.norm ℤ c ≠ 0 := Algebra.norm_ne_zero_iff.mpr hc
    have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ c| := Int.one_le_abs hz
    push_cast
    rw [← Int.cast_abs]
    exact_mod_cast h1
  -- The denominator witness `δ ∈ (𝓞 K)⁰`.
  obtain ⟨δ, hδS, hint⟩ := I.isFractional
  have hδ0 : δ ≠ 0 := nonZeroDivisors.ne_zero hδS
  set D : ℝ := mixedEmbedding.norm (mixedEmbedding K (algebraMap (𝓞 K) K δ)) with hD
  have hDpos : 0 < D := by
    rw [hD, show algebraMap (𝓞 K) K δ = ((δ : 𝓞 K) : K) from
      (RingOfIntegers.coe_eq_algebraMap δ).symm]
    exact lt_of_lt_of_le one_pos (hint_ge δ hδ0)
  refine ⟨D⁻¹, inv_pos.mpr hDpos, ?_⟩
  intro a ha ha0
  obtain ⟨c, hc⟩ := hint a ha
  -- `hc : algebraMap (𝓞 K) K c = δ • a = algebraMap δ * a`.
  have hcK : algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K δ * a := by
    rw [hc, Algebra.smul_def]
  have hc0 : c ≠ 0 := by
    intro h
    apply ha0
    have hδK : algebraMap (𝓞 K) K δ ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hδ0
    have : algebraMap (𝓞 K) K δ * a = 0 := by rw [← hcK, h, map_zero]
    exact (mul_eq_zero.mp this).resolve_left hδK
  -- Split the norm multiplicatively.
  have hsplit : mixedEmbedding.norm (mixedEmbedding K (algebraMap (𝓞 K) K c))
      = D * mixedEmbedding.norm (mixedEmbedding K a) := by
    rw [hcK, map_mul (mixedEmbedding K), map_mul]
  have hge1 : (1 : ℝ) ≤ mixedEmbedding.norm (mixedEmbedding K (algebraMap (𝓞 K) K c)) := by
    rw [show algebraMap (𝓞 K) K c = ((c : 𝓞 K) : K) from
      (RingOfIntegers.coe_eq_algebraMap c).symm]
    exact hint_ge c hc0
  rw [hsplit] at hge1
  -- From `1 ≤ D * X` and `D > 0` conclude `D⁻¹ ≤ X`.
  set X : ℝ := mixedEmbedding.norm (mixedEmbedding K a) with hX
  calc D⁻¹ = D⁻¹ * 1 := (mul_one _).symm
    _ ≤ D⁻¹ * (D * X) :=
        mul_le_mul_of_nonneg_left hge1 (inv_nonneg.mpr hDpos.le)
    _ = X := by field_simp
end DedekindZeta.ConeRadialReduction
