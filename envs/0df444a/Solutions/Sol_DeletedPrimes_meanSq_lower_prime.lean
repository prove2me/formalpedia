-- Prove2me | solution 1 for DeletedPrimes.meanSq_lower_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:12:51.231797+00:00
-- url     : https://prove2.me/submissions/ee9399f1-87d6-4723-8fc5-5f3d36bbc3e4

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
import Theorems.Thm_DeletedPrimes_IsMSRegular_mono
import Theorems.Thm_DeletedPrimes_IsRegular_mono
import Theorems.Thm_DeletedPrimes_errExp_le_maxExp
import Theorems.Thm_DeletedPrimes_frequently_dense_block
import Theorems.Thm_DeletedPrimes_kappaK_lt_half
import Theorems.Thm_DeletedPrimes_kappaK_lt_one_sub
import Theorems.Thm_DeletedPrimes_kappaK_one
import Theorems.Thm_DeletedPrimes_maxExp_neg_iff


set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) {κ ε : ℝ} (hκ0 : 0 < κ) (hκ : κ < kappaOne (dim S)) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ X : ℝ in atTop, c * X ^ (dim S * κ - ε) ≤ meanSq S X := by
  set α := dim S with hαdef
  have hκ1 : κ < kappaK 1 α := by rw [kappaK_one]; exact hκ
  set μ := -maxExp 1 α κ with hμdef
  have hμ : 0 < μ := by have := (maxExp_neg_iff le_rfl hα0 hα1).2 hκ1; linarith
  have herr : ∀ τ ∈ Set.Icc 0 κ, errExp 1 α κ τ ≤ -μ := fun τ hτ => by
    rw [hμdef, neg_neg]; exact errExp_le_maxExp le_rfl hα0 hα1 hκ0.le hτ.1 hτ.2
  have h12 : κ < 1 / 2 := lt_trans hκ1 (kappaK_lt_half le_rfl hα0 hα1)
  have h1a : κ < 1 - α := lt_trans hκ1 (kappaK_lt_one_sub le_rfl hα0 hα1)
  obtain ⟨δ, hδ, η₀, hη₀, hF⟩ := F.bound 1 le_rfl κ μ hκ0 hμ h12 h1a herr
  set η₁ := min (η₀ / 4) (min (α / 2) (ε / (2 * κ))) with hη₁def
  have hη₁0 : 0 < η₁ := lt_min (by linarith) (lt_min (by linarith) (div_pos hε (by linarith)))
  have hη₁a : η₁ ≤ η₀ / 4 := min_le_left _ _
  have hη₁b : η₁ ≤ α / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hη₁c : η₁ ≤ ε / (2 * κ) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hκη : 2 * κ * η₁ ≤ ε := by
    calc 2 * κ * η₁ ≤ 2 * κ * (ε / (2 * κ)) := mul_le_mul_of_nonneg_left hη₁c (by linarith)
      _ = ε := by field_simp
  obtain ⟨c, hc, Y₀, hY⟩ := hF (2 * η₁) (by linarith) (by linarith)
  refine ⟨c, hc, ?_⟩
  have hdense := frequently_dense_block (S := S) (σ := α - η₁) (η := η₁) (by linarith) (by linarith) hη₁0
  have hlarge : ∀ᶠ j : ℕ in atTop, Y₀ ≤ (2 : ℝ) ^ j ∧ 1 ≤ j := by
    have h2 : Tendsto (fun j : ℕ => (2 : ℝ) ^ j) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    filter_upwards [h2.eventually_ge_atTop Y₀, eventually_ge_atTop 1] with j h1 h2
    exact ⟨h1, h2⟩
  have hX : Tendsto (fun j : ℕ => ((2 : ℝ) ^ j) ^ (1 / κ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  refine hX.frequently ((hdense.and_eventually hlarge).mono fun j ⟨hd, hjY, hj1⟩ => ?_)
  set jf : Fin 1 → ℕ := fun _ => j with hjf
  have hmono : StrictMono jf := fun a b hab => absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl _)
  have hprod : ∏ i, (2 : ℝ) ^ jf i = 2 ^ j := by simp [hjf]
  have hlog : 0 < Real.log ((2 : ℝ) ^ j) := Real.log_pos (one_lt_pow₀ (by norm_num) (by omega))
  have hshare : ∀ i, |Real.log ((2 : ℝ) ^ jf i) / Real.log (∏ i', (2 : ℝ) ^ jf i') - 1 / ((1 : ℕ) : ℝ)| ≤ δ := by
    intro i
    rw [hprod]
    simp only [hjf, Nat.cast_one, div_one]
    rw [div_self hlog.ne', sub_self, abs_zero]; exact hδ.le
  have hdens : ∀ i, ((2 : ℝ) ^ jf i) ^ (α - 2 * η₁) ≤ blockCount S (2 ^ jf i) := by
    intro i
    have : α - 2 * η₁ = α - η₁ - η₁ := by ring
    simpa [hjf, this] using hd
  have key := hY jf hmono (by rw [hprod]; exact hjY) hshare hdens
  rw [hprod] at key
  simp only [hjf, Finset.univ_unique, Finset.prod_singleton] at key
  have hB : 1 ≤ ((2 : ℝ) ^ j) := one_le_pow₀ (by norm_num)
  have hXge : 1 ≤ ((2 : ℝ) ^ j) ^ (1 / κ) := Real.one_le_rpow hB (by positivity)
  have hdj : ((2 : ℝ) ^ j) ^ (α - 2 * η₁) ≤ blockCount S (2 ^ j) := by simpa [hjf] using hdens ⟨0, by omega⟩
  calc c * (((2 : ℝ) ^ j) ^ (1 / κ)) ^ (α * κ - ε)
      ≤ c * (((2 : ℝ) ^ j) ^ (1 / κ)) ^ (κ * (α - 2 * η₁)) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        exact Real.rpow_le_rpow_of_exponent_le hXge (by nlinarith)
    _ = c * ((2 : ℝ) ^ j) ^ (α - 2 * η₁) := by
        rw [← Real.rpow_mul (by positivity)]
        congr 2; field_simp
    _ ≤ c * (blockCount S (2 ^ j) : ℝ) := mul_le_mul_of_nonneg_left hdj hc.le
    _ ≤ meanSq S (((2 : ℝ) ^ j) ^ (1 / κ)) := key
end DeletedPrimes
