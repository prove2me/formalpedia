-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.RR_cN_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:38.736848+00:00
-- url     : https://prove2.me/submissions/26b95809-5896-4452-b2e7-703fd21bdb9e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_KC_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_vM_major
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_cN_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_one_le_of_exp_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_one_le_log_of_exp_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_primePowerSum_le_mul_log
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_sum_min_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
open ArithmeticFunction (vonMangoldt)
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution : ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (m₀ : ℕ) (y : ℝ), 1 ≤ y →
    (∀ p : ℕ, p.Prime → p ∣ m₀ → p ≤ ⌊x ^ 400⌋₊ → (p : ℝ) ≤ y) →
    RR (cN x) m₀ ⌊x ^ 400⌋₊ ≤ C * (Real.sqrt x + y * Real.log x) := by
  refine ⟨3 * dA_KC + 801, Real.exp 1, fun x hx m₀ y hy hpy => ?_⟩
  have hx1 := dA_one_le_of_exp_le hx
  have hlx := dA_one_le_log_of_exp_le hx
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hK := dA_KC_pos
  have hsq0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hylx : 0 ≤ y * Real.log x := mul_nonneg (by linarith) (by linarith)
  have key : ∀ S : Finset ℕ, (∀ n ∈ S, n ∈ Icc 1 ⌊x ^ 400⌋₊ ∧ (IsPrimePow n ∧
      (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀))) →
      ∑ n ∈ S, cN x n ≤ (3 * dA_KC + 801) * (Real.sqrt x + y * Real.log x) := by
    intro S hS
    have hA : ∑ n ∈ S.filter (fun n => Even (n.factorization n.minFac)), cN x n
        ≤ dA_KC * (3 * Real.sqrt x) := by
      have hsubA : S.filter (fun n => Even (n.factorization n.minFac))
          ⊆ (Icc 1 ⌊x ^ 400⌋₊).image (fun m => m ^ 2) := by
        intro n hn
        rw [Finset.mem_filter] at hn
        obtain ⟨hnS, hev⟩ := hn
        obtain ⟨hnN, hnpp, -⟩ := hS n hnS
        rw [Finset.mem_Icc] at hnN
        rw [isPrimePow_nat_iff] at hnpp
        obtain ⟨q, k, hq, hk, rfl⟩ := hnpp
        rw [hq.pow_minFac hk.ne'] at hev
        simp [Nat.factorization_pow, hq.factorization_self] at hev
        obtain ⟨j, rfl⟩ := hev
        rw [Finset.mem_image]
        have h1 : 1 ≤ q ^ j := Nat.one_le_pow _ _ hq.pos
        refine ⟨q ^ j, Finset.mem_Icc.mpr ⟨h1, ?_⟩, by show (q ^ j) ^ 2 = q ^ (j + j); ring⟩
        calc q ^ j ≤ (q ^ j) ^ 2 := by nlinarith
          _ = q ^ (j + j) := by ring
          _ ≤ _ := hnN.2
      have hgm : ∀ m : ℕ, 1 ≤ m → min 1 (x / ((m + 1 : ℕ) : ℝ) ^ 2) ≤ min 1 (x / (m : ℝ) ^ 2) := by
        intro m hm
        apply min_le_min_left
        have hm1 : (0:ℝ) < m := Nat.cast_pos.mpr (by omega)
        have hm0 : (0:ℝ) < (m:ℝ) ^ 2 := by positivity
        exact div_le_div_of_nonneg_left hx0 hm0 (by push_cast; nlinarith)
      have hmaj := dA_vM_major (fun m => min 1 (x / (m : ℝ) ^ 2))
        (fun m => le_min zero_le_one (div_nonneg hx0 (by positivity))) hgm ⌊x ^ 400⌋₊
      have hsq := dA_sum_min_sq x hx1 ⌊x ^ 400⌋₊
      calc ∑ n ∈ S.filter (fun n => Even (n.factorization n.minFac)), cN x n
          ≤ ∑ n ∈ (Icc 1 ⌊x ^ 400⌋₊).image (fun m => m ^ 2), cN x n :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubA (fun n _ _ => dA_cN_nonneg hx0 n)
        _ = ∑ m ∈ Icc 1 ⌊x ^ 400⌋₊, cN x (m ^ 2) :=
            Finset.sum_image (fun a _ b _ h => Nat.pow_left_injective (by norm_num) h)
        _ = ∑ m ∈ Icc 1 ⌊x ^ 400⌋₊, vonMangoldt m * min 1 (x / (m : ℝ) ^ 2) := by
            refine Finset.sum_congr rfl (fun m _ => ?_)
            simp only [cN, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2:ℕ) ≠ 0),
              Nat.cast_pow]
        _ ≤ dA_KC * ∑ m ∈ Icc 1 ⌊x ^ 400⌋₊, min 1 (x / (m : ℝ) ^ 2) := hmaj
        _ ≤ dA_KC * (3 * Real.sqrt x) := mul_le_mul_of_nonneg_left hsq hK.le
    have hB : ∑ n ∈ S.filter (fun n => ¬ Even (n.factorization n.minFac)), cN x n
        ≤ y * (801 * Real.log x) := by
      have hmaps : ∀ n ∈ S.filter (fun n => ¬ Even (n.factorization n.minFac)),
          n.minFac ∈ Icc 1 ⌊y⌋₊ := by
        intro n hn
        rw [Finset.mem_filter] at hn
        obtain ⟨hnS, hodd⟩ := hn
        obtain ⟨hnN, hnpp, hor⟩ := hS n hnS
        rw [Finset.mem_Icc] at hnN
        have hdvd : n.minFac ∣ m₀ := hor.resolve_left hodd
        have hpr : n.minFac.Prime := Nat.minFac_prime hnpp.ne_one
        have hle : n.minFac ≤ ⌊x ^ 400⌋₊ := (Nat.minFac_le (by omega)).trans hnN.2
        exact Finset.mem_Icc.mpr ⟨hpr.one_lt.le, Nat.le_floor (hpy n.minFac hpr hdvd hle)⟩
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      calc _ ≤ ∑ p ∈ Icc 1 ⌊y⌋₊, 801 * Real.log x := by
            refine Finset.sum_le_sum (fun p _ => ?_)
            refine le_trans ?_ (primePowerSum_le_mul_log x hx p)
            simp only [sP]
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
              (fun n _ _ => dA_cN_nonneg hx0 n)
            rw [Finset.mem_filter] at hn
            obtain ⟨hn1, hn2⟩ := hn
            rw [Finset.mem_filter] at hn1
            obtain ⟨hnS, -⟩ := hn1
            obtain ⟨hnN, hnpp, -⟩ := hS n hnS
            exact Finset.mem_filter.mpr ⟨hnN, hnpp, hn2⟩
        _ = (⌊y⌋₊ : ℝ) * (801 * Real.log x) := by simp
        _ ≤ y * (801 * Real.log x) :=
            mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (by linarith)
    rw [← Finset.sum_filter_add_sum_filter_not S (fun n => Even (n.factorization n.minFac))]
    refine (add_le_add hA hB).trans ?_
    nlinarith [mul_nonneg hK.le hylx]
  simp only [RR]
  exact key _ (fun n hn => Finset.mem_filter.mp hn)
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
