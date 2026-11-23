-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.mixedGaussian_surface_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:09:33.434515+00:00
-- url     : https://prove2.me/submissions/bf1114e4-0a83-48dc-a254-41718cae968f

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_isCompact_closure_normEqOneSurface
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
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∃ S : ℝ, 0 ≤ S ∧
      ∀ σ ∈ normEqOneSurface K,
        Summable (fun a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} =>
            Theta.mixedGaussian K (σ * mixedEmbedding K (a : K))) ∧
          (∑' a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
              Theta.mixedGaussian K (σ * mixedEmbedding K (a : K))) ≤ S := by
  classical
  -- Step 1: uniform upper bound `M ≥ 1` on every place-norm over the surface.
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ closure (normEqOneSurface K),
      ‖∑ w : InfinitePlace K, normAtPlace w x‖ ≤ C :=
    (isCompact_closure_normEqOneSurface (K := K)).exists_bound_of_continuousOn
      (by fun_prop)
  set M : ℝ := max C 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hupper : ∀ σ ∈ normEqOneSurface K, ∀ w : InfinitePlace K,
      normAtPlace w σ ≤ M := by
    intro σ hσ w
    have hsum := hC σ (subset_closure hσ)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun w _ => normAtPlace_nonneg w σ))] at hsum
    calc normAtPlace w σ
        ≤ ∑ w : InfinitePlace K, normAtPlace w σ :=
          Finset.single_le_sum (fun w _ => normAtPlace_nonneg w σ) (Finset.mem_univ w)
      _ ≤ C := hsum
      _ ≤ M := le_max_left _ _
  -- Step 2: uniform positive lower bound `κ = (M^d)⁻¹`.
  set d : ℕ := finrank ℚ K with hddef
  set κ : ℝ := (M ^ d)⁻¹ with hκdef
  have hMd : (1 : ℝ) ≤ M ^ d := one_le_pow₀ hM1
  have hκpos : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by rw [hκdef]; exact inv_le_one_of_one_le₀ hMd
  have hlower : ∀ σ ∈ normEqOneSurface K, ∀ w : InfinitePlace K,
      κ ≤ normAtPlace w σ := by
    intro σ hσ w₀
    have hnorm1 : mixedEmbedding.norm σ = 1 := (mem_normEqOneSurface.mp hσ).2
    have hne : mixedEmbedding.norm σ ≠ 0 := by rw [hnorm1]; exact one_ne_zero
    have hpos_all : ∀ w, 0 < normAtPlace w σ := by
      intro w
      refine lt_of_le_of_ne (normAtPlace_nonneg w σ) (Ne.symm ?_)
      intro h0
      exact hne (mixedEmbedding.norm_eq_zero_iff.mpr ⟨w, h0⟩)
    have hprod : ∏ w : InfinitePlace K, normAtPlace w σ ^ (mult w) = 1 := by
      rw [← mixedEmbedding.norm_apply]; exact hnorm1
    set X : ℝ := ∏ w ∈ Finset.univ.erase w₀, normAtPlace w σ ^ (mult w) with hXdef
    have hsplit : normAtPlace w₀ σ ^ (mult w₀) * X = 1 := by
      rw [hXdef, Finset.mul_prod_erase Finset.univ
        (fun w => normAtPlace w σ ^ (mult w)) (Finset.mem_univ w₀)]
      exact hprod
    have hXpos : 0 < X :=
      Finset.prod_pos (fun w _ => pow_pos (hpos_all w) _)
    have hX_le : X ≤ M ^ d := by
      have h1 : X ≤ ∏ w ∈ Finset.univ.erase w₀, M ^ (mult w) :=
        Finset.prod_le_prod (fun w _ => pow_nonneg (normAtPlace_nonneg w σ) _)
          (fun w _ => pow_le_pow_left₀ (normAtPlace_nonneg w σ) (hupper σ hσ w) _)
      have h3 : (∑ w ∈ Finset.univ.erase w₀, mult w) ≤ d := by
        rw [hddef, ← sum_mult_eq]
        exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
      calc X ≤ ∏ w ∈ Finset.univ.erase w₀, M ^ (mult w) := h1
        _ = M ^ (∑ w ∈ Finset.univ.erase w₀, mult w) := by
            rw [Finset.prod_pow_eq_pow_sum]
        _ ≤ M ^ d := pow_le_pow_right₀ hM1 h3
    -- from `p ^ m * X = 1` and `X ≤ M^d`: `κ ≤ p ^ m`.
    have ha_eq : normAtPlace w₀ σ ^ (mult w₀) = 1 / X :=
      eq_one_div_of_mul_eq_one_left hsplit
    have hpow_ge : κ ≤ normAtPlace w₀ σ ^ (mult w₀) := by
      rw [hκdef, ha_eq, show (M ^ d)⁻¹ = 1 / (M ^ d) from (one_div _).symm]
      exact one_div_le_one_div_of_le hXpos hX_le
    -- conclude `κ ≤ p` from `κ ≤ p ^ m`, `κ ≤ 1`, `m ≥ 1`.
    rcases le_total (normAtPlace w₀ σ) 1 with hp1 | hp1
    · have hpm_le : normAtPlace w₀ σ ^ (mult w₀) ≤ normAtPlace w₀ σ :=
        pow_le_of_le_one (normAtPlace_nonneg w₀ σ) hp1 mult_ne_zero
      exact le_trans hpow_ge hpm_le
    · exact le_trans hκ1 hp1
  -- Step 3: the `σ`-independent majorant point `y = κ • 1`.
  set y : mixedSpace K := (κ : ℝ) • (1 : mixedSpace K) with hydef
  have hny : ∀ w : InfinitePlace K, normAtPlace w y = κ := by
    intro w
    rw [hydef, normAtPlace_smul, map_one, mul_one, abs_of_pos hκpos]
  have hyne : mixedEmbedding.norm y ≠ 0 := by
    rw [hydef, mixedEmbedding.norm_smul, map_one, mul_one, abs_of_pos hκpos]
    exact pow_ne_zero _ hκpos.ne'
  -- Step 4: pointwise majorant bound, uniform over the surface.
  have hbound : ∀ σ ∈ normEqOneSurface K, ∀ a : K,
      Theta.mixedGaussian K (σ * mixedEmbedding K a)
        ≤ Theta.mixedGaussian K (y * mixedEmbedding K a) := by
    intro σ hσ a
    rw [Theta.mixedGaussian, Theta.mixedGaussian]
    apply Real.exp_le_exp.mpr
    have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    have hsum_le : ∑ w : InfinitePlace K,
          (mult w : ℝ) * normAtPlace w (y * mixedEmbedding K a) ^ 2
        ≤ ∑ w : InfinitePlace K,
          (mult w : ℝ) * normAtPlace w (σ * mixedEmbedding K a) ^ 2 := by
      refine Finset.sum_le_sum (fun w _ => ?_)
      have hyw : normAtPlace w (y * mixedEmbedding K a)
          = κ * normAtPlace w (mixedEmbedding K a) := by
        rw [map_mul, hny]
      have hσw : normAtPlace w (σ * mixedEmbedding K a)
          = normAtPlace w σ * normAtPlace w (mixedEmbedding K a) := by rw [map_mul]
      rw [hyw, hσw]
      have hnz : (0 : ℝ) ≤ normAtPlace w (mixedEmbedding K a) := normAtPlace_nonneg _ _
      have hle : κ * normAtPlace w (mixedEmbedding K a)
          ≤ normAtPlace w σ * normAtPlace w (mixedEmbedding K a) :=
        mul_le_mul_of_nonneg_right (hlower σ hσ w) hnz
      have hsq : (κ * normAtPlace w (mixedEmbedding K a)) ^ 2
          ≤ (normAtPlace w σ * normAtPlace w (mixedEmbedding K a)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hκpos.le hnz) hle 2
      exact mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
    nlinarith [hsum_le, Real.pi_pos]
  -- Step 5: summability + uniform tsum bound.
  set T := {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}
  let inc : T → (I : Submodule (𝓞 K) K) := fun a => ⟨a.1, a.2.1⟩
  have hinc_inj : Function.Injective inc := by
    intro a b h
    have hval : a.1 = b.1 := by simpa [inc] using h
    exact Subtype.ext hval
  -- summability of any fixed `y'` with `N y' ≠ 0`, over `T`.
  have hsummable : ∀ y' : mixedSpace K, mixedEmbedding.norm y' ≠ 0 →
      Summable (fun a : T => Theta.mixedGaussian K (y' * mixedEmbedding K (a : K))) := by
    intro y' hy'
    have hfull := Theta.summable_mixedGaussian_submodule K I hI hy'
    have hcomp := hfull.comp_injective hinc_inj
    rw [← Complex.summable_ofReal]
    exact hcomp.congr (fun a => rfl)
  -- the uniform majorant value.
  set S : ℝ := ∑' a : T, Theta.mixedGaussian K (y * mixedEmbedding K (a : K)) with hSdef
  have hSsummable : Summable (fun a : T =>
      Theta.mixedGaussian K (y * mixedEmbedding K (a : K))) := hsummable y hyne
  refine ⟨S, ?_, ?_⟩
  · rw [hSdef]
    exact tsum_nonneg (fun a => Real.exp_nonneg _)
  · intro σ hσ
    have hσne : mixedEmbedding.norm σ ≠ 0 := by
      rw [(mem_normEqOneSurface.mp hσ).2]; exact one_ne_zero
    have hσsummable := hsummable σ hσne
    refine ⟨hσsummable, ?_⟩
    rw [hSdef]
    exact hσsummable.tsum_le_tsum (fun a => hbound σ hσ (a : K)) hSsummable
end DedekindZeta.ConeRadialReduction
