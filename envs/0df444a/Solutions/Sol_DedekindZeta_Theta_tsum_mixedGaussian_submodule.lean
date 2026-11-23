-- Prove2me | solution 1 for DedekindZeta.Theta.tsum_mixedGaussian_submodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:19:17.379713+00:00
-- url     : https://prove2.me/submissions/e0708dee-367f-4a5a-932d-a435bff5017b

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussian_zero
import Theorems.Thm_DedekindZeta_Theta_summable_mixedGaussian_submodule
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0)
    {y : mixedSpace K} (hy : mixedEmbedding.norm y ≠ 0) :
    ∑' a : (J : Submodule (𝓞 K) K), (mixedGaussian K (y * mixedEmbedding K (a : K)) : ℂ)
      = 1 + mixedThetaKernel K J y := by
  classical
  set G := fun (a : (J : Submodule (𝓞 K) K)) =>
    (mixedGaussian K (y * mixedEmbedding K (a : K)) : ℂ) with hG
  have hsum : Summable G := summable_mixedGaussian_submodule K J hJ hy
  set z₀ : (J : Submodule (𝓞 K) K) := ⟨0, (J : Submodule (𝓞 K) K).zero_mem⟩ with hz₀
  rw [hsum.tsum_eq_add_tsum_ite z₀]
  have hG0 : G z₀ = 1 := by
    show (mixedGaussian K (y * mixedEmbedding K ((z₀ : (J : Submodule (𝓞 K) K)) : K)) : ℂ) = 1
    rw [show ((z₀ : (J : Submodule (𝓞 K) K)) : K) = 0 from rfl, map_zero, mul_zero,
      mixedGaussian_zero, Complex.ofReal_one]
  rw [hG0]
  congr 1
  -- The remaining `ite`-sum is the nonzero-element kernel.
  set S := {a : K // a ∈ (J : Submodule (𝓞 K) K) ∧ a ≠ 0} with hS
  let eJc : ↥(({z₀} : Set (J : Submodule (𝓞 K) K))ᶜ) ≃ S :=
  { toFun := fun a => ⟨((a : (J : Submodule (𝓞 K) K)) : K), (a : (J : Submodule (𝓞 K) K)).2, by
        intro h0
        apply a.2
        apply Subtype.ext
        exact h0⟩
    invFun := fun s => ⟨⟨s.1, s.2.1⟩, by
        intro h
        exact s.2.2 (congrArg (fun t : (J : Submodule (𝓞 K) K) => (t : K)) h)⟩
    left_inv := fun a => by apply Subtype.ext; rfl
    right_inv := fun s => by apply Subtype.ext; rfl }
  have hite : (fun a : (J : Submodule (𝓞 K) K) => ite (a = z₀) (0 : ℂ) (G a))
      = (({z₀} : Set (J : Submodule (𝓞 K) K))ᶜ).indicator G := by
    funext a
    rw [Set.indicator_apply]
    by_cases h : a = z₀
    · simp [h]
    · simp [h, Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [hite, ← tsum_subtype ({z₀} : Set (J : Submodule (𝓞 K) K))ᶜ G, mixedThetaKernel,
    ← Equiv.tsum_eq eJc (fun s => (mixedGaussian K (y * mixedEmbedding K (s : K)) : ℂ))]
  exact tsum_congr (fun x => rfl)
end DedekindZeta.Theta
