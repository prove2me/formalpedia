-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.zeta_proposition_tail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:47.640876+00:00
-- url     : https://prove2.me/submissions/491ab2b7-f8bf-46cb-b22a-2ef4a8e8388d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumLogFactorialRowsBounds
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareMomentArithmeticBound

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
set_option maxHeartbeats 800000
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : Formalism.HermitianLattices.TraceIntegrality.PropZ_tail := by
  intro C₀ hC
  refine ⟨10 + 5 * C₀, ?_⟩
  intro f nT k m t N x b a b' L v logT logg eta S sA hN hb hax hnT1 hnTf hsA0 hsA
  have hL1 := hN.one_le_L
  have hv1 := hN.one_le_v
  have hb1 := hN.one_le_b'
  have hba := hN.b'_le_a
  have hT0 := hN.logT_nonneg
  have hTle := hN.logT_le
  have hS0 := hN.S_nonneg
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hN.one_le_k
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hN.one_le_m
  have hkN : (k:ℝ) ≤ N := by
    have : k ≤ N := by rw [hN.N_eq]; exact Nat.le_add_right _ _
    exact_mod_cast this
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hN1 : (1:ℝ) ≤ N := le_trans hk1 hkN
  have hNL : (N:ℝ) * L ≤ b' := by linarith only [hN.lin, hT0]
  have hNNL : (N:ℝ) ≤ N * L := le_mul_of_one_le_right hN0 hL1
  have hkb : (k:ℝ) ≤ b' := by linarith only [hkN, hNNL, hNL]
  have hka : (k:ℝ) ≤ a := le_trans hkb hba
  have hSb : S ≤ b' := by
    have h1 := hN.small
    have h2 := hN.eta_nonneg
    have h3 : (0:ℝ) ≤ (m:ℝ) * t := by positivity
    linarith only [h1, h2, h3]
  have hnT : (1:ℝ) ≤ nT := by exact_mod_cast hnT1
  have hnT0' : (0:ℝ) ≤ nT := by linarith only [hnT]
  have hm0' : (0:ℝ) ≤ m := by linarith only [hm1]
  have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg _
  have hL0 : (0:ℝ) ≤ L := by linarith only [hL1]
  have hb0 : (0:ℝ) ≤ b' := by linarith only [hb1]
  have hk0 : (0:ℝ) ≤ k := by linarith only [hk1]
  have ha0 : (0:ℝ) ≤ a := by linarith only [hb1, hba]
  have hv0 : (0:ℝ) ≤ v := by linarith only [hv1]
  have hbS0 : (0:ℝ) ≤ b' + S := by linarith only [hb0, hS0]
  have hlogk : Real.log k ≤ L := by
    have : Real.log k ≤ Real.log (a * v) :=
      Real.log_le_log (by linarith only [hk1]) (hka.trans (le_mul_of_one_le_right ha0 hv1))
    linarith only [this, hN.log_av]
  have hlogkv0 : 0 ≤ Real.log (k * v) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hk1 hv1)
  have hlogkv : Real.log (k * v) ≤ L := by
    have : Real.log (k * v) ≤ Real.log (a * v) :=
      Real.log_le_log (mul_pos (by linarith only [hk1]) (by linarith only [hv1]))
        (mul_le_mul_of_nonneg_right hka hv0)
    linarith only [this, hN.log_av]
  have hG0 : 0 ≤ (f:ℝ) * N * b' * L := mul_nonneg (mul_nonneg (mul_nonneg hf0 hN0) hb0) hL0
  have hG : (f:ℝ) * N * b' * L ≤ f * m * N * b' * L := by
    have := mul_le_mul_of_nonneg_left hm1 hG0
    linarith only [this]
  have t1 : sA / k * logT ≤ 2 * C₀ * (a * nT * m * L / k) := by
    have s1 : sA / k ≤ 2 * a * nT / k := by gcongr
    have s0 : 0 ≤ 2 * a * nT / k :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha0) hnT0') hk0
    calc sA / k * logT ≤ 2 * a * nT / k * logT := mul_le_mul_of_nonneg_right s1 hT0
      _ ≤ 2 * a * nT / k * (C₀ * m * L) := mul_le_mul_of_nonneg_left hTle s0
      _ = 2 * C₀ * (a * nT * m * L / k) := by ring
  have t2 : (nT:ℝ) * a * Real.log k ≤ nT * a * L :=
    mul_le_mul_of_nonneg_left hlogk (mul_nonneg hnT0' ha0)
  have t6 : (nT:ℝ) * a * Real.log (k * v) ≤ nT * a * L :=
    mul_le_mul_of_nonneg_left hlogkv (mul_nonneg hnT0' ha0)
  have t3 : (f:ℝ) * k * (b' + S) * Real.log k ≤ 2 * ((f:ℝ) * N * b' * L) := by
    have u1 : (k:ℝ) * (b' + S) ≤ N * (2 * b') :=
      mul_le_mul hkN (by linarith only [hSb]) hbS0 hN0
    have u2 : (f:ℝ) * k * (b' + S) * Real.log k ≤ f * k * (b' + S) * L :=
      mul_le_mul_of_nonneg_left hlogk (mul_nonneg (mul_nonneg hf0 hk0) hbS0)
    have u3 : (f:ℝ) * (k * (b' + S)) * L ≤ f * (N * (2 * b')) * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left u1 hf0) hL0
    linarith only [u2, u3]
  have t4 : (f:ℝ) * S * logT ≤ C₀ * ((f:ℝ) * m * N * b' * L) := by
    have u1 : S * logT ≤ b' * (C₀ * m * L) := mul_le_mul hSb hTle hT0 hb0
    have u2 : (f:ℝ) * (S * logT) ≤ f * (b' * (C₀ * m * L)) := mul_le_mul_of_nonneg_left u1 hf0
    have u3 : 0 ≤ (f:ℝ) * b' * C₀ * m * L :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hf0 hb0) hC) hm0') hL0
    have u4 := mul_nonneg u3 (sub_nonneg.2 hN1)
    linarith only [u2, u4]
  have t5 : (f:ℝ) * (k:ℝ) ^ 2 * L ≤ (f:ℝ) * N * b' * L := by
    have u1 : (k:ℝ) * k ≤ N * b' := mul_le_mul hkN hkb hk0 hN0
    have u2 : (f:ℝ) * (k * k) * L ≤ f * (N * b') * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left u1 hf0) hL0
    linarith only [u2]
  have t7 : (f:ℝ) * (b' + S) * (k * Real.log (k * v) + logT)
      ≤ 2 * ((f:ℝ) * N * b' * L) + 2 * C₀ * ((f:ℝ) * m * N * b' * L) := by
    have u1 : (k:ℝ) * Real.log (k * v) ≤ N * L :=
      (mul_le_mul_of_nonneg_left hlogkv hk0).trans (mul_le_mul_of_nonneg_right hkN hL0)
    have u2 : logT ≤ C₀ * m * N * L := by
      have h0 : 0 ≤ C₀ * m * L := mul_nonneg (mul_nonneg hC hm0') hL0
      calc logT ≤ C₀ * m * L := hTle
        _ = C₀ * m * L * 1 := by ring
        _ ≤ C₀ * m * L * N := mul_le_mul_of_nonneg_left hN1 h0
        _ = C₀ * m * N * L := by ring
    have u3 : 0 ≤ (k:ℝ) * Real.log (k * v) + logT := by
      have h0 := mul_nonneg hk0 hlogkv0
      linarith only [h0, hT0]
    have u4 : (b' + S) * ((k:ℝ) * Real.log (k * v) + logT) ≤ (2 * b') * (N * L + C₀ * m * N * L) :=
      mul_le_mul (by linarith only [hSb]) (by linarith only [u1, u2]) u3 (by linarith only [hb0])
    have u5 := mul_le_mul_of_nonneg_left u4 hf0
    linarith only [u5]
  have hD : (0:ℝ) < nT * m * b :=
    mul_pos (mul_pos (by linarith only [hnT]) (by linarith only [hm1])) hb
  rw [div_le_iff₀ hD]
  have hm0 : (m:ℝ) ≠ 0 := (by linarith only [hm1] : (0:ℝ) < m).ne'
  have hk0' : (k:ℝ) ≠ 0 := (by linarith only [hk1] : (0:ℝ) < k).ne'
  have hnT0 : (nT:ℝ) ≠ 0 := (by linarith only [hnT] : (0:ℝ) < nT).ne'
  have hb0' : b ≠ 0 := hb.ne'
  have hE : (10 + 5 * C₀) * (x * L / m + x * L / k + f * N * b' * L / (nT * b)) * (nT * m * b)
      = (10 + 5 * C₀) * (a * nT * L + a * nT * m * L / k + f * m * N * b' * L) := by
    rw [hax]
    field_simp
  rw [hE]
  have hQ1 : 0 ≤ a * nT * L := mul_nonneg (mul_nonneg ha0 hnT0') hL0
  have hQ2 : 0 ≤ a * nT * m * L / k :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ha0 hnT0') hm0') hL0) hk0
  have hQ3 : 0 ≤ (f:ℝ) * m * N * b' * L := by linarith only [hG0, hG]
  have r1 := mul_nonneg hC hQ1
  have r2 := mul_nonneg hC hQ2
  have r3 := mul_nonneg hC hQ3
  linarith only [t1, t2, t3, t4, t5, t6, t7, hG, hQ1, hQ2, hQ3, r1, r2, r3]
end Formalism.HermitianLattices.TraceIntegrality
