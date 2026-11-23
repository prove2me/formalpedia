-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.lin_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:55.761029+00:00
-- url     : https://prove2.me/submissions/a94d20a0-4b5d-492d-b1aa-3f497507a067

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_sum_pairs_reindex
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_shift_bound1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_shift_bound2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_harm_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (J : ℕ) (hJ : 1 ≤ J) (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) :
    |∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, (de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))| ≤
      (1 + J * Real.log 2) / 4 := by
  rw [sum_pairs_reindex]
  set B : ℕ → ℝ := fun d => ∑ i ∈ Icc 1 (J - d), (de (i + d) - de i) with hB
  have h1 : ∀ d ∈ Ioc 0 J, ∑ i ∈ Icc 1 (J - d),
      (de (i + d) - de i) / (4 * (((i + d : ℕ) : ℝ) - (i : ℝ))) = B d / (4 * d) := by
    intro d _
    rw [hB]; simp only
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1; push_cast; ring
  rw [Finset.sum_congr rfl h1]
  set h : ℕ := (J + 1) / 2 with hh
  have hh1 : 1 ≤ h := by omega
  have hhJ : h ≤ J := by omega
  have hJ2 : J ≤ 2 * h := by omega
  have h2J : 2 * h ≤ J + 1 := by omega
  have hJ2R : (J : ℝ) ≤ 2 * h := by exact_mod_cast hJ2
  have h2JR : 2 * (h : ℝ) ≤ J + 1 := by exact_mod_cast h2J
  have hhpos : (0 : ℝ) < h := by exact_mod_cast hh1
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  calc |∑ d ∈ Ioc 0 J, B d / (4 * d)| ≤ ∑ d ∈ Ioc 0 J, |B d / (4 * d)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ Ioc 0 h, |B d / (4 * d)| + ∑ d ∈ Ioc h J, |B d / (4 * d)| :=
        (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hhJ).symm
    _ ≤ ∑ _d ∈ Ioc 0 h, (1 / 4 : ℝ) + ∑ d ∈ Ioc h J, ((J : ℝ) / 4 * (1 / d) - 1 / 4) := by
        refine add_le_add (Finset.sum_le_sum fun d hd => ?_) (Finset.sum_le_sum fun d hd => ?_)
        · rw [mem_Ioc] at hd
          have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * d), div_le_iff₀ (by positivity)]
          have := shift_bound1 de h01 (J - d) d
          linarith
        · rw [mem_Ioc] at hd
          have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * d), div_le_iff₀ (by positivity)]
          have := shift_bound2 de h01 (J - d) d
          rw [Nat.cast_sub hd.2] at this
          have e : ((J : ℝ) / 4 * (1 / d) - 1 / 4) * (4 * d) = J - d := by field_simp
          rw [e]; exact this
    _ = (h : ℝ) / 4 + ((J : ℝ) / 4 * ∑ d ∈ Ioc h J, (1 : ℝ) / d - ((J : ℝ) - h) / 4) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub hhJ]
        simp; ring
    _ ≤ (h : ℝ) / 4 + ((J : ℝ) / 4 * Real.log 2 - ((J : ℝ) - h) / 4) := by
        have h3 := harm_log h J hh1 hhJ
        have h4 : Real.log J - Real.log h ≤ Real.log 2 := by
          rw [← Real.log_div (ne_of_gt hJpos) (ne_of_gt hhpos)]
          apply Real.log_le_log (by positivity)
          rw [div_le_iff₀ hhpos]; exact hJ2R
        have h5 : (J : ℝ) / 4 * ∑ d ∈ Ioc h J, (1 : ℝ) / d ≤ (J : ℝ) / 4 * Real.log 2 :=
          mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
        linarith
    _ ≤ (1 + J * Real.log 2) / 4 := by linarith
end Formalism.FourierDecayAlt.P.Sz4
