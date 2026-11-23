-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.first_zeta_arithmetic_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:37.537796+00:00
-- url     : https://prove2.me/submissions/ab4d8624-0c99-4013-acec-1d4c7a80e08d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumLogFactorialRowsBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : ZetaValueArithmetic := by
  intro C₀ hC
  refine ⟨8 * C₀ + 11, ?_⟩
  intro ι _ N N' m n logHook logOm v L logT logg logK logh logh' lev logBlock logThn logS2 logTh
    hf hN hNN hm hv hL hT hg hlf hlN hlv hmax hK hh hh' hlev hBlock hThn hS2
  have hf1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hf
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNN' : (N : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hNN
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsum : ∑ τ, ((N : ℝ) * N') * Real.log (2 * Real.exp 1 * max 1 ((n τ : ℝ) / ((N : ℝ) * N')))
      ≤ (Fintype.card ι : ℝ) * ((N : ℝ) * N') * (2 + C₀ * L) := by
    calc _ ≤ ∑ _τ : ι, ((N : ℝ) * N') * (2 + C₀ * L) := by
          apply sum_le_sum
          intro τ _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hmx : 0 < max 1 ((n τ : ℝ) / ((N : ℝ) * N')) := lt_of_lt_of_le one_pos (le_max_left _ _)
          rw [Real.log_mul (by positivity) hmx.ne', Real.log_mul (by norm_num) (Real.exp_pos 1).ne',
            Real.log_exp]
          have := Real.log_two_lt_d9
          linarith [hmax τ]
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring
  generalize (∑ τ, ((N : ℝ) * N') * Real.log (2 * Real.exp 1 * max 1 ((n τ : ℝ) / ((N : ℝ) * N')))) = J
    at hsum hThn
  generalize (∑ τ, (logHook τ - n τ * logOm τ)) = Sg at hBlock ⊢
  generalize (Fintype.card ι : ℝ) = f at *
  generalize (N : ℝ) = Nr at *
  generalize (N' : ℝ) = Nr' at *
  generalize (m : ℝ) = mr at *
  have hN'1 : 1 ≤ Nr' := hN1.trans hNN'
  have hf0 : 0 < f := by linarith
  have hN0 : 0 < Nr := by linarith
  have hN'0 : 0 < Nr' := by linarith
  have hv0 : 0 < v := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hlN0 : Real.log Nr ≤ L := (Real.log_le_log hN0 hNN').trans hlN
  have hl2 := Real.log_two_lt_d9
  have hl4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hl16 : Real.log 16 ≤ 3 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith
  have hx1 : 1 ≤ f * Nr * Nr' * v := by
    have h1 : 1 ≤ f * Nr := one_le_mul_of_one_le_of_one_le hf1 hN1
    have h2 : 1 ≤ f * Nr * Nr' := one_le_mul_of_one_le_of_one_le h1 hN'1
    exact one_le_mul_of_one_le_of_one_le h2 hv
  have hbig : Real.log (2 + 8 * (f * Nr * Nr') * v) ≤ 3 + 4 * L := by
    calc Real.log (2 + 8 * (f * Nr * Nr') * v) ≤ Real.log (16 * (f * Nr * Nr' * v)) := by
          apply Real.log_le_log (by positivity); linarith
      _ = Real.log 16 + (Real.log f + Real.log Nr + Real.log Nr' + Real.log v) := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) hv0.ne',
            Real.log_mul (by positivity) hN'0.ne', Real.log_mul hf0.ne' hN0.ne']
      _ ≤ 3 + 4 * L := by linarith
  have hfN : Real.log (f * Nr') ≤ 2 * L := by
    rw [Real.log_mul hf0.ne' hN'0.ne']; linarith
  have hE0 : 0 ≤ L + logT + logg := by linarith
  have hm2 : 1 ≤ mr ^ 2 := one_le_pow₀ hm1
  have hP0 : 0 ≤ f * mr ^ 2 * Nr' ^ 2 := by positivity
  have a1 : f * Nr' ^ 2 ≤ f * mr ^ 2 * Nr' ^ 2 := by
    have : f * Nr' ^ 2 * 1 ≤ f * Nr' ^ 2 * mr ^ 2 := by gcongr
    linarith
  have a2 : f * Nr * Nr' ≤ f * Nr' ^ 2 := by
    have : f * Nr * Nr' ≤ f * Nr' * Nr' := by gcongr
    linarith [this, sq Nr']
  have a3 : f * Nr' ≤ f * Nr' ^ 2 := by
    have : f * Nr' * 1 ≤ f * Nr' * Nr' := by gcongr
    nlinarith [this]
  have a4 : f * (mr ^ 2 * Nr + Nr * Nr') ≤ 2 * (f * mr ^ 2 * Nr' ^ 2) := by
    have h1 : f * (mr ^ 2 * Nr) ≤ f * (mr ^ 2 * Nr' ^ 2) := by
      have : Nr ≤ Nr' ^ 2 := by nlinarith
      gcongr
    have h2 : f * (Nr * Nr') ≤ f * mr ^ 2 * Nr' ^ 2 := by linarith
    linarith
  have t1 : f * Nr' ^ 2 * (L + logT + logg) ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul_of_nonneg_right a1 hE0
  have t2 : f * Nr' * L ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul (a3.trans a1) (by linarith) hL0 hP0
  have t3 : f * Nr' * logT ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul (a3.trans a1) (by linarith) hT hP0
  have t4 : f * (mr ^ 2 * Nr + Nr * Nr') * logg
      ≤ 2 * (f * mr ^ 2 * Nr' ^ 2) * (L + logT + logg) :=
    mul_le_mul a4 (by linarith) hg (by positivity)
  have t5 : f * Nr * Nr' * L ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul (a2.trans a1) (by linarith) hL0 hP0
  have t6 : f * Nr * Nr' * 1 ≤ f * mr ^ 2 * Nr' ^ 2 * (L + logT + logg) :=
    mul_le_mul (a2.trans a1) (by linarith) zero_le_one hP0
  have c1 := mul_le_mul_of_nonneg_left t1 hC
  have c2 := mul_le_mul_of_nonneg_left t2 hC
  have c3 := mul_le_mul_of_nonneg_left t3 hC
  have c4 := mul_le_mul_of_nonneg_left t4 hC
  have c5 := mul_le_mul_of_nonneg_left t5 hC
  have e1 : C₀ * f * Nr' * Real.log (f * Nr') ≤ C₀ * f * Nr' * (2 * L) := by gcongr
  have e2 : (f * Nr * Nr') * Real.log 4 ≤ (f * Nr * Nr') * 2 := by gcongr
  have e3 : (f * Nr * Nr') * Real.log (2 + 8 * (f * Nr * Nr') * v) ≤ (f * Nr * Nr') * (3 + 4 * L) := by
    gcongr
  generalize Real.log (f * Nr') = z1 at *
  generalize Real.log 4 = z2 at *
  generalize Real.log (2 + 8 * (f * Nr * Nr') * v) = z3 at *
  linarith
end Formalism.HermitianLattices.TraceIntegrality
