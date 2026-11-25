-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.term_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:31.243801+00:00
-- url     : https://prove2.me/submissions/0a7e0c60-17d8-4a8d-ad48-16f9a6c56719

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Complex Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
private theorem hH_eq_harmonic' (k : ℕ) : hH k = ((harmonic k : ℚ) : ℝ) := by
  unfold hH
  rw [harmonic_eq_sum_Icc,
    show Finset.Ioc 0 k = Finset.Icc 1 k by
      ext a
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega]
  push_cast
  rfl
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
end
end

set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
theorem _root_.solution (N U b : ℕ) (hb : 1 ≤ b) (hbU : b ≤ U) (hUN : U * U ≤ N) :
    |hH (N / b) - (Real.log N + Real.eulerMascheroniConstant - Real.log b)| ≤ 2 * b / N := by
  have hbpos : 0 < b := by omega
  have hbb : b * b ≤ N := le_trans (Nat.mul_le_mul hbU hbU) hUN
  have hk1 : 1 ≤ N / b := by
    rw [Nat.le_div_iff_mul_le hbpos]
    nlinarith
  have hdm := Nat.div_add_mod N b
  have hml := Nat.mod_lt N hbpos
  have hkb : N / b * b ≤ N := Nat.div_mul_le_self N b
  have hNlt : N < (N / b + 1) * b := by nlinarith
  have hk0 : N / b ≠ 0 := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by nlinarith)
  have hkR : (1 : ℝ) ≤ ((N / b : ℕ) : ℝ) := by exact_mod_cast hk1
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hkbR : ((N / b : ℕ) : ℝ) * b ≤ N := by exact_mod_cast hkb
  have hNltR : (N : ℝ) < (((N / b : ℕ) : ℝ) + 1) * b := by exact_mod_cast hNlt
  have hHk : hH (N / b) = ((harmonic (N / b) : ℚ) : ℝ) := hH_eq_harmonic' (N / b)
  have hA1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' (N / b)
  have hA2 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant (N / b)
  simp only [Real.eulerMascheroniSeq', Real.eulerMascheroniSeq, hk0, if_false] at hA1 hA2
  rw [← hHk] at hA1 hA2
  set K : ℝ := ((N / b : ℕ) : ℝ) with hK
  have hlog1 : Real.log (K + 1) - Real.log K ≤ 1 / K := by
    rw [← Real.log_div (by positivity) (by positivity), add_div, div_self (by positivity)]
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / K by positivity)
    linarith
  have hlogB1 : Real.log K + Real.log b - Real.log N ≤ 0 := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    linarith [Real.log_le_log (by positivity) hkbR]
  have hlogB2 : -(1 / K) ≤ Real.log K + Real.log b - Real.log N := by
    have h1 : Real.log N < Real.log ((K + 1) * b) := Real.log_lt_log hN0 hNltR
    rw [Real.log_mul (by positivity) (by positivity)] at h1
    linarith
  have hfin : 1 / K ≤ 2 * b / N := by
    rw [le_div_iff₀ hN0, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  rw [abs_le]
  constructor <;> linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
