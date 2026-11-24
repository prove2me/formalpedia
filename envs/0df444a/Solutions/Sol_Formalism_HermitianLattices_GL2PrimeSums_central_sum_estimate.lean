-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.central_sum_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:42:58.088024+00:00
-- url     : https://prove2.me/submissions/1191c52b-c9ed-45db-8ba4-72eec2889990

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_pointwise
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_comb
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_expand
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_cn_nonneg
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_cn_le
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_le_log
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_diag_eq
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_log_le_sqrt
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_diag_le
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_R_le
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_restrict2
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_W_le
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5_mean_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GL2PrimeSums
theorem _root_.solution : JacobiTwistedMeanSquareBound := by
  intro hψ ε hε0 hε1 C' c' hC' hc'
  refine ⟨max 3 (Real.exp (800 / c')), 4 * C' + 1286, ?_⟩
  intro x hx m₀ PPs κ nStar _ _ hm₀p hne hPP _ _ hκn hμ
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp (800 / c') ≤ x := (le_max_right _ _).trans hx
  have he : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL1 : 1 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact he
  have hLc : 800 / c' ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hxe
  have hψN : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ) := by
    intro M
    have := hψ M (Nat.cast_nonneg M)
    rwa [Nat.floor_natCast] at this
  have hcard : (0 : ℝ) < PPs.card := by exact_mod_cast Finset.card_pos.2 hne
  simp only [sqSum]
  set N := ⌊x ^ (400 : ℝ)⌋₊ with hN
  have hNz : (N : ℝ) ≤ x ^ (400 : ℝ) := Nat.floor_le (by positivity)
  set δ := C' * Real.exp (-c' * Real.log x ^ 2) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hcn0 : ∀ n, 0 ≤ cn x n := gl2a5_cn_nonneg hx0.le

  have ha : ∀ n, ‖(cn x n : ℂ) * κ n‖ ≤ cn x n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hcn0 n)]
    exact mul_le_of_le_one_right (hcn0 n) (hκn n)
  have step1 := gl2a5_expand (Icc 1 N) PPs (fun n => (cn x n : ℂ) * κ n) (cn x) ha
  have step2 : (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, cn x n * cn x n' *
      |∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)|) / PPs.card =
      ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, cn x n * cn x n' *
        |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card| := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro n _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro n' _
    rw [abs_div, Nat.abs_cast, mul_div_assoc]
  have step3 := gl2a5_restrict2 x N
    (fun n n' => |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card|)
  have step4 := gl2a5_comb (primesLeFinset N) (cn x) hcn0 (outPart m₀) Nat.minFac
    (fun n n' => (∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card) δ
    nStar.minFac (nStar / nStar.minFac) (by
      intro n hn n' hn'
      have hn2 := mem_filter.1 hn
      have hn2' := mem_filter.1 hn'
      exact gl2a5_pointwise m₀ nStar hn2.2 hn2'.2 _ δ hδ0 (gl2a5_mean_le_one PPs _)
        (fun h1 h2 => hμ n n' hn2.1 hn2'.1 hn2.2 hn2'.2 h1 h2))
  rw [gl2a5_diag_eq] at step4

  set s := Real.sqrt x with hs
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 hx1
  have hss : s * s = x := Real.mul_self_sqrt hx0.le
  have hLs : Real.log x ≤ 2 * s := gl2a5_log_le_sqrt hx1
  have hD := gl2a5_diag_le hψN hx3 N
  have hsum : ∑ n ∈ primesLeFinset N, cn x n ≤ 2 * x ^ (400 : ℝ) := by
    calc ∑ n ∈ primesLeFinset N, cn x n ≤ ∑ n ∈ Icc 1 N, cn x n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => hcn0 n)
      _ ≤ ∑ n ∈ Icc 1 N, Λ n := Finset.sum_le_sum (fun n _ => gl2a5_cn_le x n)
      _ ≤ 2 * (N : ℝ) := hψN N
      _ ≤ _ := by linarith
  have hsum0 : 0 ≤ ∑ n ∈ primesLeFinset N, cn x n := Finset.sum_nonneg (fun n _ => hcn0 n)
  have hgen : δ * (∑ n ∈ primesLeFinset N, cn x n) ^ 2 ≤ 4 * C' := by
    have h1 : (∑ n ∈ primesLeFinset N, cn x n) ^ 2 ≤ (2 * x ^ (400 : ℝ)) ^ 2 := pow_le_pow_left₀ hsum0 hsum 2
    have h2 : (2 * x ^ (400 : ℝ)) ^ 2 = 4 * Real.exp (800 * Real.log x) := by
      rw [Real.rpow_def_of_pos hx0, mul_pow, ← Real.exp_nat_mul]
      norm_num
      ring_nf
    have h3 : Real.exp (-c' * Real.log x ^ 2) * Real.exp (800 * Real.log x) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      have h4 : 800 ≤ c' * Real.log x := by
        rw [div_le_iff₀ hc'] at hLc; linarith
      nlinarith
    calc δ * (∑ n ∈ primesLeFinset N, cn x n) ^ 2 ≤ δ * (4 * Real.exp (800 * Real.log x)) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hδ0
      _ = 4 * C' * (Real.exp (-c' * Real.log x ^ 2) * Real.exp (800 * Real.log x)) := by
          rw [hδ]; ring
      _ ≤ 4 * C' * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 4 * C' := by ring
  have hR := gl2a5_R_le hψN he N m₀ (x ^ (ε / 5)) (by positivity) (by
    intro p hp hd hpN
    rcases hm₀p p hp hd with h | h
    · exact h
    · exfalso
      have : (p : ℝ) ≤ N := by exact_mod_cast hpN
      linarith)
  have hY : x ^ (ε / 5) * (3 * Real.log x) ≤ 10 * s := by
    have h1 : x ^ (ε / 5) ≤ x ^ ((1 : ℝ) / 5) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h2 : Real.log x ≤ x ^ ((3 : ℝ) / 10) / (3 / 10) :=
      Real.log_le_rpow_div hx0.le (by norm_num)
    have h3 : x ^ ((1 : ℝ) / 5) * x ^ ((3 : ℝ) / 10) = s := by
      rw [← Real.rpow_add hx0, hs, Real.sqrt_eq_rpow]; norm_num
    have h4 : 3 * Real.log x ≤ 10 * x ^ ((3 : ℝ) / 10) := by
      have : x ^ ((3 : ℝ) / 10) / (3 / 10) = 10 / 3 * x ^ ((3 : ℝ) / 10) := by ring
      linarith
    calc x ^ (ε / 5) * (3 * Real.log x) ≤ x ^ ((1 : ℝ) / 5) * (10 * x ^ ((3 : ℝ) / 10)) :=
          mul_le_mul h1 h4 (by positivity) (by positivity)
      _ = 10 * (x ^ ((1 : ℝ) / 5) * x ^ ((3 : ℝ) / 10)) := by ring
      _ = 10 * s := by rw [h3]
  set R := ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = 1), cn x n with hRdef
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun n _ => hcn0 n)
  have hR16 : R ≤ 16 * s := by linarith
  have hW : ∀ d, ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = d), cn x n ≤ 22 * s := by
    intro d
    have h1 := gl2a5_W_le hx0.le N m₀ d
    have h2 := gl2a5s_le_log he N d
    linarith
  have hW0 : ∀ d, 0 ≤ ∑ n ∈ (primesLeFinset N).filter (fun n => outPart m₀ n = d), cn x n :=
    fun d => Finset.sum_nonneg (fun n _ => hcn0 n)
  have hWW := mul_le_mul (hW nStar.minFac) (hW (nStar / nStar.minFac)) (hW0 _) (by positivity)
  have hRR : R ^ 2 ≤ (16 * s) ^ 2 := pow_le_pow_left₀ hR0 hR16 2
  have hxL : x ≤ x * Real.log x := le_mul_of_one_le_right hx0.le hL1
  have hfin : (∑ q ∈ PPs, ‖∑ n ∈ Icc 1 N, (cn x n : ℂ) * κ n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2) /
      PPs.card ≤ ∑ n ∈ primesLeFinset N, ∑ n' ∈ primesLeFinset N, cn x n * cn x n' *
        |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card| := by
    rw [← step3, ← step2]
    exact div_le_div_of_nonneg_right step1 hcard.le
  refine hfin.trans (step4.trans ?_)
  have e1 : (16 * s) ^ 2 = 256 * x := by rw [mul_pow, sq s, hss]; norm_num
  have e2 : 22 * s * (22 * s) = 484 * x := by rw [← hss]; ring
  rw [e1] at hRR
  rw [e2] at hWW
  have hC'x : 4 * C' ≤ 4 * C' * (x * Real.log x) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  nlinarith
end Formalism.HermitianLattices.GL2PrimeSums
