-- Prove2me | solution 1 for EulerMascheroni.Mixed.mixed_value_coefficient_sum
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T14:25:42.122322+00:00
-- url     : https://prove2.me/submissions/c7b0eb15-4ba8-40fd-855b-97a9ec46c276

import Definitions.Def_eulerMascheroni_mixedCoefficients
set_option maxHeartbeats 1000000
open EulerMascheroni.Mixed
open scoped Topology
namespace EulerSumWork
lemma exp_hasSum : HasSum (fun n : ℕ => (1 : ℂ)/(n.factorial:ℂ)) (Complex.exp 1) := by
  simpa only [one_pow, Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (1:ℂ)
lemma ein_summable_norm : Summable (fun n => ‖einCoefficient n‖) := by
  apply (summable_nat_add_iff 1).mp
  have hbound : Summable (fun n : ℕ => (1:ℝ)/((n+1).factorial:ℝ)) := by
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial 1)
  apply hbound.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  simp only [einCoefficient, norm_div, norm_pow, norm_neg, norm_one, one_pow,
    norm_mul, Complex.norm_natCast]
  gcongr
  push_cast
  nlinarith [mul_nonneg (show (0:ℝ) ≤ n by positivity)
    (show (0:ℝ) ≤ ((n+1).factorial:ℝ) by positivity)]
lemma ein_hasSum : HasSum einCoefficient (ein 1) := by
  have h := summable_norm_iff.mp ein_summable_norm
  have heq : (∑' n, einCoefficient n) = ein 1 := by
    simpa [ein, einCoefficient] using (h.sum_add_tsum_nat_add 1).symm
  exact heq ▸ h.hasSum
lemma value_hasSum (a b c : ℝ) :
    HasSum (valueCoefficient a b c)
      ((a:ℂ)+(b:ℂ)*Complex.exp 1+(c:ℂ)*expEin 1) := by
  have hexp : Summable (fun n : ℕ => ‖(1:ℂ)/(n.factorial:ℂ)‖) := by
    simpa using (Real.summable_pow_div_factorial 1)
  have hconv := hasSum_sum_range_mul_of_summable_norm hexp ein_summable_norm
  rw [exp_hasSum.tsum_eq, ein_hasSum.tsum_eq] at hconv
  convert ((hasSum_ite_eq 0 (a:ℂ)).add (exp_hasSum.mul_left (b:ℂ))).add
    (hconv.mul_left (c:ℂ)) using 1
  · funext n
    simp [valueCoefficient, div_eq_mul_inv]
  · rfl
lemma value_zero (a b c : ℝ) : valueCoefficient a b c 0 = (a:ℂ)+(b:ℂ) := by
  simp [valueCoefficient,einCoefficient]
end EulerSumWork

theorem solution (a b c : ℝ) :
    HasSum (EulerMascheroni.Mixed.valueCoefficient a b c)
      ((a:ℂ)+(b:ℂ)*Complex.exp 1+(c:ℂ)*EulerMascheroni.Mixed.expEin 1) ∧
    EulerMascheroni.Mixed.valueCoefficient a b c 0 = (a:ℂ)+(b:ℂ) := by
  exact ⟨EulerSumWork.value_hasSum a b c, EulerSumWork.value_zero a b c⟩

#print axioms solution
