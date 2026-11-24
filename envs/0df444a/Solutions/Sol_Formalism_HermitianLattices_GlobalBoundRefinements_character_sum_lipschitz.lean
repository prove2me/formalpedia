-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.character_sum_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:46.549929+00:00
-- url     : https://prove2.me/submissions/22c9c54e-ec72-42de-8ef9-4d2db760e554

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GlobalBoundRefinements
open Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GlobalBoundRefinements
theorem _root_.solution : LipschitzWeightedSums := by
  have hinv : ∀ u v : ℝ, 0 < u → u ≤ v → ∀ c : ℝ, 0 ≤ c → c / v ≤ c / u := by
    intro u v hu huv c hc
    have h1 := one_div_le_one_div_of_le hu huv
    calc c / v = c * (1 / v) := by ring
      _ ≤ c * (1 / u) := mul_le_mul_of_nonneg_left h1 hc
      _ = c / u := by ring
  have hnr : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := by
    intro r
    first
    | exact Complex.norm_real r
    | simp
    | exact Complex.abs_ofReal r
  refine ⟨?_, ?_⟩
  · intro a S ha A w₀ w₁ w₂ hw₀ h01 h12 h2A
    have hw₁ : 0 < w₁ := lt_of_lt_of_le hw₀ h01
    have hw₂ : 0 < w₂ := lt_of_lt_of_le hw₁ h12
    have hA : 0 < A := lt_of_lt_of_le hw₂ h2A
    have hform : ∀ w : ℝ, 0 < w → (w : ℂ) * Gchi a S (A / w)
        = ∑ n ∈ Icc 1 ⌊A / w⌋₊, a n * ((A / n - w : ℝ) : ℂ) - (A : ℂ) * S := by
      intro w hw
      have hwne : w ≠ 0 := hw.ne'
      have hwC : (w : ℂ) ≠ 0 := by exact_mod_cast hwne
      have h1 : (w : ℂ) * ∑ n ∈ Icc 1 ⌊A / w⌋₊, a n * ((A / w / n - 1 : ℝ) : ℂ)
          = ∑ n ∈ Icc 1 ⌊A / w⌋₊, a n * ((A / n - w : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        have e : w * (A / w / n - 1) = A / n - w := by
          rw [mul_sub, mul_one, div_div, mul_div_assoc', mul_div_mul_left _ _ hwne]
        rw [← e]
        push_cast
        ring
      have h2 : (w : ℂ) * (((A / w : ℝ) : ℂ) * S) = (A : ℂ) * S := by
        rw [← mul_assoc]
        congr 1
        push_cast
        first
        | (field_simp; ring)
        | field_simp
      simp only [Gchi]
      rw [mul_sub, h1, h2]
    have hq : A / w₂ ≤ A / w₁ := hinv w₁ w₂ hw₁ h12 A hA.le
    have hN21 : ⌊A / w₂⌋₊ ≤ ⌊A / w₁⌋₊ := Nat.floor_mono hq
    have hsplit : Icc 1 ⌊A / w₁⌋₊ = Icc 1 ⌊A / w₂⌋₊ ∪ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Icc 1 ⌊A / w₂⌋₊) (Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_Icc] at hx1
      rw [Finset.mem_Ioc] at hx2
      omega
    have hU : ∑ n ∈ Icc 1 ⌊A / w₁⌋₊, a n * ((A / n - w₁ : ℝ) : ℂ)
        = ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * ((A / n - w₁ : ℝ) : ℂ)
          + ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * ((A / n - w₁ : ℝ) : ℂ) := by
      rw [hsplit, Finset.sum_union hdisj]
    have hD : ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * ((A / n - w₂ : ℝ) : ℂ)
        - ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * ((A / n - w₁ : ℝ) : ℂ)
        = ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * ((w₁ - w₂ : ℝ) : ℂ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      push_cast
      ring
    have hX : ‖∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * ((w₁ - w₂ : ℝ) : ℂ)‖
        ≤ ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, ‖a n‖ * (w₂ - w₁) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => ?_))
      rw [norm_mul, hnr, abs_of_nonpos (by linarith)]
      exact le_of_eq (by ring)
    have hY : ‖∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * ((A / n - w₁ : ℝ) : ℂ)‖
        ≤ ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, ‖a n‖ * (w₂ - w₁) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
      rw [Finset.mem_Ioc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlow : w₁ ≤ A / n := by
        have h1 : (n : ℝ) ≤ A / w₁ :=
          le_trans (by exact_mod_cast hn.2) (Nat.floor_le (div_nonneg hA.le hw₁.le))
        rw [le_div_iff₀ hn0]
        rw [le_div_iff₀ hw₁] at h1
        linarith
      have hup : A / n < w₂ := by
        have h1 : A / w₂ < (n : ℝ) := by
          have h3 := Nat.lt_floor_add_one (A / w₂)
          have h2 : ((⌊A / w₂⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn.1
          linarith
        rw [div_lt_iff₀ hn0]
        rw [div_lt_iff₀ hw₂] at h1
        linarith
      rw [norm_mul, hnr, abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    have hsum : ∑ n ∈ Icc 1 ⌊A / w₁⌋₊, ‖a n‖ ≤ 2 * (A / w₁) := ha (A / w₁) (div_nonneg hA.le hw₁.le)
    rw [hsplit, Finset.sum_union hdisj] at hsum
    have hAw : A / w₁ ≤ A / w₀ := hinv w₀ w₁ hw₀ h01 A hA.le
    have hAw0 : 0 ≤ A / w₀ := div_nonneg hA.le hw₀.le
    have hS : (∑ n ∈ Icc 1 ⌊A / w₂⌋₊, ‖a n‖ * (w₂ - w₁))
        + ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, ‖a n‖ * (w₂ - w₁)
        = (∑ n ∈ Icc 1 ⌊A / w₂⌋₊, ‖a n‖ + ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, ‖a n‖) * (w₂ - w₁) := by
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]
    rw [hform w₂ hw₂, hform w₁ hw₁]
    calc ‖_‖ = ‖∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * ((w₁ - w₂ : ℝ) : ℂ)
          - ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * ((A / n - w₁ : ℝ) : ℂ)‖ := by
          congr 1
          linear_combination hD - hU
      _ ≤ ‖∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * ((w₁ - w₂ : ℝ) : ℂ)‖
          + ‖∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * ((A / n - w₁ : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ (∑ n ∈ Icc 1 ⌊A / w₂⌋₊, ‖a n‖ * (w₂ - w₁))
          + ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, ‖a n‖ * (w₂ - w₁) := add_le_add hX hY
      _ = (∑ n ∈ Icc 1 ⌊A / w₂⌋₊, ‖a n‖ + ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, ‖a n‖) * (w₂ - w₁) := hS
      _ ≤ (2 * (A / w₀)) * (w₂ - w₁) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ 3 * A / w₀ * (w₂ - w₁) := by
          have e : 3 * A / w₀ = 3 * (A / w₀) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  · intro a ha0 ha A w₀ w₁ w₂ hw₀ h01 h12 h2A
    have hw₁ : 0 < w₁ := lt_of_lt_of_le hw₀ h01
    have hw₂ : 0 < w₂ := lt_of_lt_of_le hw₁ h12
    have hA : 0 < A := lt_of_lt_of_le hw₂ h2A
    have hform : ∀ w : ℝ, 0 < w → w * Gone a (A / w)
        = ∑ n ∈ Icc 1 ⌊A / w⌋₊, a n * (A / n - w)
          - A * (Real.log (A / w) - 1 - Real.eulerMascheroniConstant) := by
      intro w hw
      have hwne : w ≠ 0 := hw.ne'
      have h1 : w * ∑ n ∈ Icc 1 ⌊A / w⌋₊, a n * (A / w / n - 1)
          = ∑ n ∈ Icc 1 ⌊A / w⌋₊, a n * (A / n - w) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        have e : w * (A / w / n - 1) = A / n - w := by
          rw [mul_sub, mul_one, div_div, mul_div_assoc', mul_div_mul_left _ _ hwne]
        rw [← e]
        ring
      have hwA : w * (A / w) = A := by
        first
        | (field_simp; ring)
        | field_simp
      have h2 : w * (A / w * (Real.log (A / w) - 1 - Real.eulerMascheroniConstant))
          = A * (Real.log (A / w) - 1 - Real.eulerMascheroniConstant) := by
        rw [← mul_assoc, hwA]
      simp only [Gone]
      rw [mul_sub, h1, h2]
    have hq : A / w₂ ≤ A / w₁ := hinv w₁ w₂ hw₁ h12 A hA.le
    have hN21 : ⌊A / w₂⌋₊ ≤ ⌊A / w₁⌋₊ := Nat.floor_mono hq
    have hsplit : Icc 1 ⌊A / w₁⌋₊ = Icc 1 ⌊A / w₂⌋₊ ∪ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Icc 1 ⌊A / w₂⌋₊) (Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_Icc] at hx1
      rw [Finset.mem_Ioc] at hx2
      omega
    have hbd : ∀ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, w₁ ≤ A / n ∧ A / n < w₂ := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlow : w₁ ≤ A / n := by
        have h1 : (n : ℝ) ≤ A / w₁ :=
          le_trans (by exact_mod_cast hn.2) (Nat.floor_le (div_nonneg hA.le hw₁.le))
        rw [le_div_iff₀ hn0]
        rw [le_div_iff₀ hw₁] at h1
        linarith
      have hup : A / n < w₂ := by
        have h1 : A / w₂ < (n : ℝ) := by
          have h3 := Nat.lt_floor_add_one (A / w₂)
          have h2 : ((⌊A / w₂⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn.1
          linarith
        rw [div_lt_iff₀ hn0]
        rw [div_lt_iff₀ hw₂] at h1
        linarith
      exact ⟨hlow, hup⟩
    have hU : ∑ n ∈ Icc 1 ⌊A / w₁⌋₊, a n * (A / n - w₁)
        = ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * (A / n - w₁)
          + ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * (A / n - w₁) := by
      rw [hsplit, Finset.sum_union hdisj]
    have hD : ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * (A / n - w₂)
        - ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n * (A / n - w₁)
        = (∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n) * (w₁ - w₂) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      ring
    have hY0 : 0 ≤ ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * (A / n - w₁) := by
      apply Finset.sum_nonneg
      intro n hn
      exact mul_nonneg (ha0 n) (by linarith [(hbd n hn).1])
    have hY1 : ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * (A / n - w₁)
        ≤ (∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n) * (w₂ - w₁) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left (by linarith [(hbd n hn).2]) (ha0 n)
    have hsum : ∑ n ∈ Icc 1 ⌊A / w₁⌋₊, a n ≤ 2 * (A / w₁) := ha (A / w₁) (div_nonneg hA.le hw₁.le)
    rw [hsplit, Finset.sum_union hdisj] at hsum
    have hS2 : 0 ≤ ∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n := Finset.sum_nonneg (fun n _ => ha0 n)
    have hSI : 0 ≤ ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n := Finset.sum_nonneg (fun n _ => ha0 n)
    have hAw : A / w₁ ≤ A / w₀ := hinv w₀ w₁ hw₀ h01 A hA.le
    have hAw0 : 0 ≤ A / w₀ := div_nonneg hA.le hw₀.le
    have hLd : Real.log (A / w₁) - Real.log (A / w₂) = Real.log w₂ - Real.log w₁ := by
      rw [Real.log_div hA.ne' hw₁.ne', Real.log_div hA.ne' hw₂.ne']
      ring
    have hl0 : 0 ≤ Real.log w₂ - Real.log w₁ := by
      have := Real.log_le_log hw₁ h12
      linarith
    have hl1 : Real.log w₂ - Real.log w₁ ≤ (w₂ - w₁) / w₀ := by
      have h3 := Real.log_le_sub_one_of_pos (div_pos hw₂ hw₁)
      rw [Real.log_div hw₂.ne' hw₁.ne'] at h3
      have e : (w₂ - w₁) / w₁ = w₂ / w₁ - 1 := by rw [sub_div, div_self hw₁.ne']
      have h4 : (w₂ - w₁) / w₁ ≤ (w₂ - w₁) / w₀ := hinv w₀ w₁ hw₀ h01 (w₂ - w₁) (by linarith)
      linarith
    have hAl0 : 0 ≤ A * (Real.log w₂ - Real.log w₁) := mul_nonneg hA.le hl0
    have hAl1 : A * (Real.log w₂ - Real.log w₁) ≤ A * ((w₂ - w₁) / w₀) :=
      mul_le_mul_of_nonneg_left hl1 hA.le
    have hP1 : 0 ≤ (∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n) * (w₂ - w₁) := mul_nonneg hS2 (by linarith)
    have hP2 : ((∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n) + ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n) * (w₂ - w₁)
        ≤ (2 * (A / w₀)) * (w₂ - w₁) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hR : 3 * A / w₀ * (w₂ - w₁) = (2 * (A / w₀)) * (w₂ - w₁) + A * ((w₂ - w₁) / w₀) := by ring
    have hnn : 0 ≤ (2 * (A / w₀)) * (w₂ - w₁) := mul_nonneg (by linarith) (by linarith)
    rw [hform w₂ hw₂, hform w₁ hw₁]
    calc |_| = |(∑ n ∈ Icc 1 ⌊A / w₂⌋₊, a n) * (w₁ - w₂)
          - ∑ n ∈ Ioc ⌊A / w₂⌋₊ ⌊A / w₁⌋₊, a n * (A / n - w₁)
          + A * (Real.log w₂ - Real.log w₁)| := by
          congr 1
          rw [← hLd]
          linear_combination hD - hU
      _ ≤ 3 * A / w₀ * (w₂ - w₁) := by
          rw [abs_le, hR]
          constructor <;> linarith
end Formalism.HermitianLattices.GlobalBoundRefinements
