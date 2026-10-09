-- Prove2me | solution 1 for BookProof.ChapterE.exp_J
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:27:06.346887+00:00
-- url     : https://prove2.me/submissions/126c53e9-4f20-4d0a-8b8b-3fff0efba3b7

-- Generated from ChapterE.lean — solution of BookProof.ChapterE.exp_J
import Mathlib
import Definitions.Def_ChapterE
open BookProof.ChapterE



open scoped Matrix BigOperators
open Filter
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) :
    NormedSpace.exp (t • J) = !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t] := by

  -- By definition of matrix exponential, we know that
  have h_exp : NormedSpace.exp (t • J) = ∑' n, (t ^ n / Nat.factorial n) • (J ^ n) := by
    simp only [div_eq_inv_mul];
    convert NormedSpace.exp_eq_tsum using 3;
    constructor;
    · exact fun _ 𝕂 {_} _ _ _ _ _ _ ↦ NormedSpace.exp_eq_tsum 𝕂;
    intro h; rw [ h ℝ ] ; simp [ mul_comm, smul_pow ] ;
    simp [ mul_comm, smul_smul ];
  -- We'll use the fact that $J^2 = -I$ to simplify the series.
  have h_simp : ∀ n : ℕ, J ^ (2 * n) = (-1 : ℝ) ^ n • 1 ∧ J ^ (2 * n + 1) = (-1 : ℝ) ^ n • J := by
    intro n; induction n <;> simp_all [ Nat.mul_succ, pow_succ, pow_mul ] ;
    simp_all [ show J * J = -1 from by ext i j; fin_cases i <;> fin_cases j <;> norm_num [ J ] ];
  -- Let's split the sum into two parts: one for even $n$ and one for odd $n$.
  have h_split : ∑' n, (t ^ n / Nat.factorial n) • (J ^ n) =
      (∑' n, (t ^ (2 * n) / Nat.factorial (2 * n)) • (J ^ (2 * n))) +
        (∑' n, (t ^ (2 * n + 1) / Nat.factorial (2 * n + 1)) • (J ^ (2 * n + 1))) := by
    rw [ ← tsum_even_add_odd ];
    · simp_all only [] ;
      have := Real.hasSum_cos t;
      convert this.summable.smul_const ( 1 : Matrix ( Fin 2 ) ( Fin 2 ) ℝ ) using 2 ; ring;
      rw [ smul_smul, mul_comm ];
    · simp_all only [← smul_assoc, smul_eq_mul];
      refine Summable.smul_const ?_ _
      refine Summable.of_norm ?_
      simp
      have base := Real.summable_pow_div_factorial (|t| : ℝ)
      refine Summable.comp_injective base ?_
      intro m n h
      simpa using h
  simp_all only [← smul_assoc, smul_eq_mul];
  -- Recognize that the sums are the Taylor series for $\cos t$ and $\sin t$.
  have h_cos_sin :
      (∑' n, (t ^ (2 * n) / Nat.factorial (2 * n)) * (-1) ^ n) = Real.cos t ∧
        (∑' n, (t ^ (2 * n + 1) / Nat.factorial (2 * n + 1)) * (-1) ^ n) = Real.sin t := by
    constructor
    · rw [ Real.cos_eq_tsum ]
      exact tsum_congr fun n => by ring
    · rw [ Real.sin_eq_tsum ]
      exact tsum_congr fun n => by ring
  rw [ Summable.tsum_smul_const, Summable.tsum_smul_const ] ;
  focus (norm_num [ h_cos_sin ]);
  · ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ J ];
  · refine Summable.of_norm ?_
    simp
    have base := Real.summable_pow_div_factorial (|t| : ℝ)
    refine Summable.comp_injective base ?_
    intro m n h
    simpa using h
  · refine Summable.of_norm ?_
    simp
    have base := Real.summable_pow_div_factorial (|t| : ℝ)
    refine Summable.comp_injective base ?_
    intro m n h
    simpa using h
