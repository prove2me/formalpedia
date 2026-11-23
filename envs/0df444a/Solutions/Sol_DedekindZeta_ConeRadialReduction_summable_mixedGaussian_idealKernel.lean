-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.summable_mixedGaussian_idealKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:09:49.399061+00:00
-- url     : https://prove2.me/submissions/4eaf6041-e19c-4a99-a396-82055734e004

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_summable_mixedGaussian_submodule
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
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥)
    {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    Summable (fun a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} =>
      Theta.mixedGaussian K (x * mixedEmbedding K ((a : 𝓞 K) : K))) := by
  set J : FractionalIdeal (𝓞 K)⁰ K := (𝔞 : FractionalIdeal (𝓞 K)⁰ K) with hJ
  have hJ0 : J ≠ 0 := (FractionalIdeal.coeIdeal_ne_zero).mpr h𝔞
  have hmem : ∀ a : 𝓞 K, a ∈ 𝔞 → (a : K) ∈ (J : Submodule (𝓞 K) K) := by
    intro a ha
    rw [FractionalIdeal.mem_coe, hJ, RingOfIntegers.coe_eq_algebraMap]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ ha
  have hC := Theta.summable_mixedGaussian_submodule K J hJ0 hx
  let f : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0} → (J : Submodule (𝓞 K) K) :=
    fun a => ⟨(a.1 : K), hmem a.1 a.2.1⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have hval : ((f a : (J : Submodule (𝓞 K) K)) : K) = ((f b : (J : Submodule (𝓞 K) K)) : K) :=
      congrArg (fun t : (J : Submodule (𝓞 K) K) => (t : K)) hab
    exact Subtype.ext (RingOfIntegers.coe_injective hval)
  have hCsub := hC.comp_injective hfinj
  rw [← Complex.summable_ofReal]
  exact hCsub
end DedekindZeta.ConeRadialReduction
