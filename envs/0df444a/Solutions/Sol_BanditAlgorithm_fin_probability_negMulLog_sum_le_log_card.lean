-- Prove2me | solution 1 for BanditAlgorithm.fin_probability_negMulLog_sum_le_log_card
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T23:25:57.964176+00:00
-- url     : https://prove2.me/submissions/b33e6fad-3239-4a4f-b817-93365e9275fe

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open scoped BigOperators

namespace BanditAlgorithm

theorem _root_.solution {k : ℕ} [NeZero k]
    (p : Fin k → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    ∑ a, Real.negMulLog (p a) ≤ Real.log k := by
  classical
  have hk0 : 0 < (k : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hkw : ∑ _a : Fin k, (1 / (k : ℝ)) = 1 := by
    simp [hk0.ne']
  have hj := Real.convexOn_mul_log.map_sum_le
    (t := Finset.univ) (w := fun _a : Fin k ↦ 1 / (k : ℝ))
    (p := p) (fun _ _ ↦ by positivity) hkw
    (fun a _ ↦ Set.mem_Ici.mpr (hp0 a))
  have hmean : ∑ a : Fin k, (1 / (k : ℝ)) • p a = 1 / (k : ℝ) := by
    simp only [smul_eq_mul]
    rw [← Finset.mul_sum, hp1, mul_one]
  rw [hmean] at hj
  have hcalc : (1 / (k : ℝ)) * Real.log (1 / (k : ℝ)) = -Real.log k / k := by
    rw [Real.log_div (by norm_num) hk0.ne']
    simp [hk0.ne']
    field_simp
  rw [hcalc] at hj
  have hscale :
      ∑ a : Fin k, (1 / (k : ℝ)) • (p a * Real.log (p a)) =
        -(1 / (k : ℝ)) * ∑ a, Real.negMulLog (p a) := by
    simp only [smul_eq_mul, Finset.mul_sum]
    simp only [Real.negMulLog]
    ring
  rw [hscale] at hj
  have hj' : -Real.log k / k ≤ -(∑ a, Real.negMulLog (p a)) / k :=
    hj.trans_eq (by ring)
  have hscaled := (div_le_div_iff_of_pos_right hk0).mp hj'
  linarith

end BanditAlgorithm
