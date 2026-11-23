-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.exists_pos_lower_mixedQuadForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:34:43.273832+00:00
-- url     : https://prove2.me/submissions/dfc9c080-0487-4eb8-8b51-188b2c4451de

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_isCompact_closure_normEqOneSurface
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
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ q : ℝ, 0 < q ∧ ∀ σ ∈ normEqOneSurface K,
      ∀ a : 𝓞 K, a ∈ 𝔞 → a ≠ 0 →
        q ≤ mixedQuadForm K (σ * mixedEmbedding K ((a : 𝓞 K) : K)) := by
  classical
  -- Step 1: a uniform upper bound `M ≥ 1` on every place-norm over the surface
  -- (same mechanism as in `mixedGaussian_surface_majorant`).
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
  -- Step 2: uniform positive lower bound `κ = (M^d)⁻¹` on every place-norm.
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
    have ha_eq : normAtPlace w₀ σ ^ (mult w₀) = 1 / X :=
      eq_one_div_of_mul_eq_one_left hsplit
    have hpow_ge : κ ≤ normAtPlace w₀ σ ^ (mult w₀) := by
      rw [hκdef, ha_eq, show (M ^ d)⁻¹ = 1 / (M ^ d) from (one_div _).symm]
      exact one_div_le_one_div_of_le hXpos hX_le
    rcases le_total (normAtPlace w₀ σ) 1 with hp1 | hp1
    · have hpm_le : normAtPlace w₀ σ ^ (mult w₀) ≤ normAtPlace w₀ σ :=
        pow_le_of_le_one (normAtPlace_nonneg w₀ σ) hp1 mult_ne_zero
      exact le_trans hpow_ge hpm_le
    · exact le_trans hκ1 hp1
  -- Step 3: the uniform lower bound is `q = κ²`.
  refine ⟨κ ^ 2, by positivity, ?_⟩
  intro σ hσ a ha𝔞 ha0
  set P : mixedSpace K := mixedEmbedding K ((a : 𝓞 K) : K) with hPdef
  -- `|N a| ≥ 1`, hence `∏_w ‖P‖_w^{mult w} ≥ 1` and `P ≠ 0`.
  have h1le : (1 : ℝ) ≤ |Algebra.norm ℚ ((a : 𝓞 K) : K)| := by
    rw [← Algebra.coe_norm_int, ← Int.cast_one, ← Int.cast_abs, Rat.cast_intCast, Int.cast_le]
    exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha0)
  have hnormP : mixedEmbedding.norm P = |Algebra.norm ℚ ((a : 𝓞 K) : K)| :=
    mixedEmbedding.norm_eq_norm _
  have hPne : mixedEmbedding.norm P ≠ 0 := by
    rw [hnormP]; exact ne_of_gt (lt_of_lt_of_le one_pos h1le)
  have hpos : ∀ w : InfinitePlace K, 0 < normAtPlace w P := by
    intro w
    refine lt_of_le_of_ne (normAtPlace_nonneg w P) (Ne.symm ?_)
    intro h0
    exact hPne (mixedEmbedding.norm_eq_zero_iff.mpr ⟨w, h0⟩)
  have hprodP : (1 : ℝ) ≤ ∏ w : InfinitePlace K, normAtPlace w P ^ (mult w) := by
    rw [← mixedEmbedding.norm_apply, hnormP]; exact h1le
  -- There is a place `w₀` with `‖P‖_{w₀} ≥ 1`.
  obtain ⟨w₀, hw₀⟩ : ∃ w : InfinitePlace K, 1 ≤ normAtPlace w P := by
    by_contra h
    push_neg at h
    have hlt : ∏ w : InfinitePlace K, normAtPlace w P ^ (mult w) < 1 := by
      calc ∏ w : InfinitePlace K, normAtPlace w P ^ (mult w)
          < ∏ _w : InfinitePlace K, (1 : ℝ) :=
            Finset.prod_lt_prod_of_nonempty
              (fun w _ => pow_pos (hpos w) _)
              (fun w _ => pow_lt_one₀ (normAtPlace_nonneg w P) (h w) mult_ne_zero)
              Finset.univ_nonempty
        _ = 1 := by simp
    exact absurd hprodP (not_le.mpr hlt)
  -- Conclude: `Q(σ·P) ≥ mult w₀ · (‖σ‖_{w₀}·‖P‖_{w₀})² ≥ κ²`.
  have hterm : κ ^ 2 ≤ (mult w₀ : ℝ) * normAtPlace w₀ (σ * P) ^ 2 := by
    have hmap : normAtPlace w₀ (σ * P) = normAtPlace w₀ σ * normAtPlace w₀ P := by
      rw [map_mul]
    have e2 : κ ≤ normAtPlace w₀ σ := hlower σ hσ w₀
    have hb : κ ≤ normAtPlace w₀ σ * normAtPlace w₀ P := by
      calc κ = κ * 1 := (mul_one κ).symm
        _ ≤ normAtPlace w₀ σ * normAtPlace w₀ P :=
          mul_le_mul e2 hw₀ zero_le_one (le_trans hκpos.le e2)
    have hsq : κ ^ 2 ≤ (normAtPlace w₀ σ * normAtPlace w₀ P) ^ 2 :=
      pow_le_pow_left₀ hκpos.le hb 2
    rw [hmap]
    calc κ ^ 2 = 1 * κ ^ 2 := (one_mul _).symm
      _ ≤ (mult w₀ : ℝ) * (normAtPlace w₀ σ * normAtPlace w₀ P) ^ 2 :=
        mul_le_mul one_le_mult hsq (sq_nonneg _) (le_trans zero_le_one one_le_mult)
  have hsum_ge : (mult w₀ : ℝ) * normAtPlace w₀ (σ * P) ^ 2
      ≤ ∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ) * normAtPlace w (σ * P) ^ 2 :=
    Finset.single_le_sum
      (f := fun w : InfinitePlace K => (InfinitePlace.mult w : ℝ) * normAtPlace w (σ * P) ^ 2)
      (fun w _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Finset.mem_univ w₀)
  calc κ ^ 2 ≤ (mult w₀ : ℝ) * normAtPlace w₀ (σ * P) ^ 2 := hterm
    _ ≤ mixedQuadForm K (σ * P) := hsum_ge
end DedekindZeta.ConeRadialReduction
