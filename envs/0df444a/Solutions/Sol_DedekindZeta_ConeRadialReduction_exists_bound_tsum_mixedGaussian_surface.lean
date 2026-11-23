-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.exists_bound_tsum_mixedGaussian_surface
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:37:35.462809+00:00
-- url     : https://prove2.me/submissions/9b6430e2-aff8-4912-9855-e5687178f15d

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedGaussian_surface_majorant
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedGaussian_nonneg
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
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ ∈ normEqOneSurface K,
      ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
        Theta.mixedGaussian K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) ≤ M := by
  -- Reproved by the termwise-majorant
  -- route, staying inside the nonzero-norm locus: NOT the unsound global
  -- continuity / closure-maximum argument. The integer-indexed sum over the
  -- nonzero elements of `𝔞` injects into the fractional-ideal-indexed sum over
  -- `(𝔞 : FractionalIdeal)`, for which `mixedGaussian_surface_majorant` already
  -- supplies a uniform `σ`-independent bound `S` (a single convergent Gaussian
  -- lattice majorant via the uniform place-norm lower bound `κ`). Comparing the
  -- two tsums termwise (all summands nonnegative) through that injection gives
  -- the same bound for the integer-indexed sum.
  classical
  by_cases h𝔞 : 𝔞 = ⊥
  · -- the zero ideal: the index set is empty, so the sum is `0`.
    subst h𝔞
    refine ⟨0, le_refl 0, ?_⟩
    intro σ _
    have hempty : IsEmpty {a : 𝓞 K // a ∈ (⊥ : Ideal (𝓞 K)) ∧ a ≠ 0} := by
      constructor
      rintro ⟨a, ha, hne⟩
      rw [Ideal.mem_bot] at ha
      exact hne ha
    rw [tsum_empty]
  · set J : FractionalIdeal (𝓞 K)⁰ K := (𝔞 : FractionalIdeal (𝓞 K)⁰ K) with hJ
    have hJ0 : J ≠ 0 := (FractionalIdeal.coeIdeal_ne_zero).mpr h𝔞
    obtain ⟨S, hS, hSbound⟩ := mixedGaussian_surface_majorant J hJ0
    refine ⟨S, hS, ?_⟩
    intro σ hσ
    obtain ⟨hσsum, hσle⟩ := hSbound σ hσ
    -- the injection `{a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} ↪ {a : K // a ∈ J ∧ a ≠ 0}`.
    have hmem : ∀ a : 𝓞 K, a ∈ 𝔞 → (a : K) ∈ (J : Submodule (𝓞 K) K) := by
      intro a ha
      rw [FractionalIdeal.mem_coe, hJ, RingOfIntegers.coe_eq_algebraMap]
      exact FractionalIdeal.mem_coeIdeal_of_mem _ ha
    set i : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} →
        {a : K // a ∈ (J : Submodule (𝓞 K) K) ∧ a ≠ 0} :=
      fun a => ⟨(a.1 : K), hmem a.1 a.2.1,
        (RingOfIntegers.coe_ne_zero_iff).mpr a.2.2⟩ with hidef
    have hiinj : Function.Injective i := by
      intro a b hab
      have hval : ((i a).1) = ((i b).1) := congrArg Subtype.val hab
      exact Subtype.ext (RingOfIntegers.coe_injective hval)
    -- compare the integer-indexed tsum with the submodule-indexed tsum.
    have hcomp := tsum_comp_le_tsum_of_inj hσsum
      (fun a => mixedGaussian_nonneg (σ * mixedEmbedding K (a : K))) hiinj
    calc ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
            Theta.mixedGaussian K (σ * mixedEmbedding K ((a : 𝓞 K) : K))
        = ∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
            Theta.mixedGaussian K (σ * mixedEmbedding K ((i a).1)) := rfl
      _ ≤ ∑' a : {a : K // a ∈ (J : Submodule (𝓞 K) K) ∧ a ≠ 0},
            Theta.mixedGaussian K (σ * mixedEmbedding K (a : K)) := hcomp
      _ ≤ S := hσle
end DedekindZeta.ConeRadialReduction
