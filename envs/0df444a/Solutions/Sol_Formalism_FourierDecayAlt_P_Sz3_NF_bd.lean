-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.NF_bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:34.421241+00:00
-- url     : https://prove2.me/submissions/5b45c9dc-fd64-4156-8301-357718888e44

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_hs_tail
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_hs_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_hs_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_Icc_one_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_diff_bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution (J : ℕ) (hJ : 1 ≤ J) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) :
    |NF J de| ≤ 7 / 10 * (J : ℝ) + 1 := by
  unfold NF
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ : ∃ p : ℕ, 1 ≤ p ∧ p ≤ J ∧ J ≤ 2 * p ∧ 2 * p ≤ J + 1 :=
    ⟨(J + 1) / 2, by omega, by omega, by omega, by omega⟩
  rw [Icc_one_eq J, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le p) hp2]
  have hA : ∑ d ∈ Ioc 0 p, |(∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i) / (d : ℝ)| ≤
      ∑ _d ∈ Ioc 0 p, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro d hd
    simp only [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    rw [abs_div, abs_of_pos hd0, div_le_one hd0]
    exact (diff_bd J d (by omega) de hde).1
  have hB : ∑ d ∈ Ioc p J, |(∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i) / (d : ℝ)| ≤
      ∑ d ∈ Ioc p J, ((J : ℝ) * (1 / (d : ℝ)) - 1) := by
    apply Finset.sum_le_sum
    intro d hd
    simp only [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by
      have : 0 < d := by omega
      exact_mod_cast this
    rw [abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
    have := (diff_bd J d hd.2 de hde).2
    have e : ((J : ℝ) * (1 / (d : ℝ)) - 1) * d = J - d := by field_simp
    rw [e]; exact this
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs_sub p J hp2] at hB
  simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, Nat.sub_zero] at hA hB
  rw [Nat.cast_sub hp2] at hB
  have ht := hs_tail p hp1
  have hm := hs_mono J (2 * p) hp3
  have hpos : (0 : ℝ) < 1 / (4 * (p : ℝ) + 1) := by positivity
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have h7 : hs J - hs p ≤ 7 / 10 := by linarith
  have hmul : (J : ℝ) * (hs J - hs p) ≤ J * (7 / 10) := mul_le_mul_of_nonneg_left h7 hJ0
  have hp4R : 2 * (p : ℝ) ≤ J + 1 := by exact_mod_cast hp4
  linarith
end Formalism.FourierDecayAlt.P.Sz3
