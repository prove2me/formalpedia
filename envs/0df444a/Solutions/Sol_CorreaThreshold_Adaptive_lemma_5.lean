-- Prove2me | solution 1 for CorreaThreshold.Adaptive.lemma_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:56:03.888281+00:00
-- url     : https://prove2.me/submissions/3f488a23-7470-4118-967d-6817fc3f7bd7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting
import Theorems.Thm_CorreaThreshold_Adaptive_lemma_4
import Theorems.Thm_CorreaThreshold_Adaptive_eq_7
import Theorems.Thm_CorreaThreshold_Adaptive_rho_equal_iff

open MeasureTheory ProbabilityTheory CorreaThreshold.Adaptive

lemma correa2_sum_pieces (ε : ℕ → ℝ) (n : ℕ) (hεmono : ∀ i < n, ε i < ε (i + 1))
    (h : ℝ → ENNReal) :
    ∀ k ≤ n, ∑ i ∈ Finset.Icc 1 k, ∫⁻ q in Set.Icc (ε (i - 1)) (ε i), h q =
      ∫⁻ q in Set.Ioc (ε 0) (ε k), h q := by
  have hmono : ∀ k ≤ n, ε 0 ≤ ε k := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih => intro hk; exact le_trans (ih (by omega)) (hεmono k (by omega)).le
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [Finset.sum_Icc_succ_top (by omega), ih (by omega), Nat.add_sub_cancel,
      setLIntegral_congr (Ioc_ae_eq_Icc (μ := volume)).symm,
      ← lintegral_union measurableSet_Ioc, Set.Ioc_union_Ioc_eq_Ioc (hmono k (by omega))
        (hεmono k (by omega)).le]
    exact Set.disjoint_left.2 (fun x h1 h2 => by linarith [h1.2, h2.1])

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (ε : ℕ → ℝ) (hε0 : ε 0 = 0) (hεn : ε n = 1)
    (hεmono : ∀ i < n, ε i < ε (i + 1))
    (hρ : ∀ i ∈ Finset.Icc 1 n, rho n ε i = rho n ε 1) :
    SamuelCahnProphet.IID.Emax μ n = ENNReal.ofReal (n * gam n ε 1) * quantileValue μ n ε := by
  have h4 := lemma_4 μ hμ hn ε hε0 hεn hεmono
  have h7 := (eq_7 μ hμ hn).2.2.2
  have hγ : gam n ε 1 = 1 - (1 - ε 1) ^ (n - 1) := (rho_equal_iff hn ε hε0 hεn hεmono).2.2
  -- `0 < ε 1 ≤ 1`, hence `γ₁ > 0`
  have hle : ∀ k, 1 + k ≤ n → ε 1 ≤ ε (1 + k) := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih => intro hk; exact le_trans (ih (by omega)) (hεmono (1 + k) (by omega)).le
  have hε1 : ε 1 ≤ 1 := by
    have := hle (n - 1) (by omega)
    rwa [show 1 + (n - 1) = n by omega, hεn] at this
  have hε1' : 0 < ε 1 := by have := hεmono 0 (by omega); rwa [hε0] at this
  have hγpos : 0 < gam n ε 1 := by
    rw [hγ]
    have : (1 - ε 1) ^ (n - 1) < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
    linarith
  have hρ1 : rho n ε 1 = 1 / gam n ε 1 := rfl
  -- rewrite the quantile value
  have hq : quantileValue μ n ε = ENNReal.ofReal (1 / gam n ε 1) *
      ∫⁻ q in Set.Ioc 0 1, ENNReal.ofReal (psi n q) * Rq μ q := by
    have hsum := correa2_sum_pieces ε n hεmono (fun q => ENNReal.ofReal (psi n q) * Rq μ q) n le_rfl
    rw [hε0, hεn] at hsum
    rw [h4, ← hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hρ i hi, hρ1]
  -- rewrite `E max`
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hE : SamuelCahnProphet.IID.Emax μ n = ENNReal.ofReal n *
      ∫⁻ q in Set.Ioc 0 1, ENNReal.ofReal (psi n q) * Rq μ q := by
    rw [h7, setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume)), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro q
    rw [ENNReal.ofReal_mul hn0, mul_assoc]
  rw [hE, hq, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp
