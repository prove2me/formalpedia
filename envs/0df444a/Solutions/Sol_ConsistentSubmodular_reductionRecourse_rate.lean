-- Prove2me | solution 1 for ConsistentSubmodular.reductionRecourse_rate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:18.823771+00:00
-- url     : https://prove2.me/submissions/1fa4f948-7c38-4f48-8803-889b37a014fb

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RecourseBound
import Theorems.Thm_ConsistentSubmodular_reductionRecourse_le

section

noncomputable section

namespace ConsistentSubmodular

theorem accuracy_ge (ε : ℝ) : 200 ≤ accuracy ε := Nat.le_add_left _ _

theorem accuracy_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : (accuracy ε : ℝ) ≤ 220 / ε := by
  unfold accuracy
  push_cast
  have hfl : (⌊20 / ε⌋₊ : ℝ) ≤ 20 / ε := Nat.floor_le (by positivity)
  have h200 : (200 : ℝ) ≤ 200 / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hsplit : (220 : ℝ) / ε = 20 / ε + 200 / ε := by ring
  linarith

theorem rateConstant_nonneg (C : ℕ) : 0 ≤ rateConstant C := by
  unfold rateConstant
  have h : 0 ≤ Real.log (1200 * ((C : ℝ) + 1)) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ C := Nat.cast_nonneg C
    nlinarith)
  positivity

theorem log_le_six_add_log_inv {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hN : 1 ≤ N)
    (hNle : (N : ℝ) ≤ 220 / ε) : Real.log N ≤ 6 + Real.log (1 / ε) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Real.log_le_log hNr hNle
  rw [show (220 : ℝ) / ε = 220 * (1 / ε) by ring,
    Real.log_mul (by norm_num) (by positivity)] at h
  have h220 : Real.log 220 ≤ 6 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h6]
    nlinarith [pow_le_pow_left₀ (by norm_num) he.le 6]
  linarith

theorem quarter_le_log_inv {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 3 / 4) :
    1 / 4 ≤ Real.log (1 / ε) := by
  have h := Real.log_le_sub_one_of_pos hε
  have hinv : Real.log (1 / ε) = -Real.log ε := by rw [one_div, Real.log_inv]
  rw [hinv]
  linarith

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution (C : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 3 / 4) :
    (reductionRecourse (accuracy ε) ((C + 1) * (3 * accuracy ε + 2)) : ℝ) ≤
      reductionConstant C * (1 / ε) ^ 3 * Real.log (1 / ε) := by
  obtain ⟨N, hNdef⟩ : ∃ N, N = accuracy ε := ⟨_, rfl⟩
  rw [← hNdef]
  have hN1 : 1 ≤ N := by rw [hNdef]; exact (show 1 ≤ 200 by norm_num).trans (accuracy_ge ε)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNle : (N : ℝ) ≤ 220 / ε := by rw [hNdef]; exact accuracy_le hε (by linarith)
  have hbase := reductionRecourse_le C N hN1
  have hA := rateConstant_nonneg C
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hlogN := log_le_six_add_log_inv hε hN1 hNle
  have hlogε := quarter_le_log_inv hε hε1.le
  have hN3 : (N : ℝ) ^ 3 ≤ (220 / ε) ^ 3 :=
    pow_le_pow_left₀ (by linarith) hNle 3
  have hfactor : 0 ≤ rateConstant C + 800 * Real.log N := by linarith
  have hpow : 0 ≤ (220 / ε) ^ 3 := pow_nonneg (div_nonneg (by norm_num) hε.le) 3
  calc (reductionRecourse N ((C + 1) * (3 * N + 2)) : ℝ)
      ≤ (N : ℝ) ^ 3 * (rateConstant C + 800 * Real.log N) := hbase
    _ ≤ (220 / ε) ^ 3 * (rateConstant C + 800 * (6 + Real.log (1 / ε))) :=
        mul_le_mul hN3 (by linarith) hfactor hpow
    _ ≤ (220 / ε) ^ 3 * ((4 * rateConstant C + 20000) * Real.log (1 / ε)) := by
        apply mul_le_mul_of_nonneg_left _ hpow
        nlinarith
    _ = reductionConstant C * (1 / ε) ^ 3 * Real.log (1 / ε) := by
        unfold reductionConstant
        ring

end
