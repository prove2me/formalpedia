-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.exponential_tail_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:46.983468+00:00
-- url     : https://prove2.me/submissions/68ec7535-7d62-410f-a8ec-78a2c1b6c3f3

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GaussianIntegralFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : ExponentialTailIntegral := by
  intro n α hn hα
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set β : ℝ := α - ((n : ℝ) - 1) with hβ
  have hβ1 : 1 ≤ β := by rw [hβ]; linarith
  have hneg : -β < 0 := by linarith
  have hint : IntegrableOn (fun s : ℝ => Real.exp (-((n : ℝ) - 1)) * Real.exp (-β * s)) (Set.Ioi 1) :=
    (integrableOn_exp_mul_Ioi hneg 1).const_mul _
  have hle : ∫ s in Set.Ioi (1 : ℝ), s ^ (n - 1) * Real.exp (-(α * s)) ≤
      ∫ s in Set.Ioi (1 : ℝ), Real.exp (-((n : ℝ) - 1)) * Real.exp (-β * s) := by
    refine integral_mono_of_nonneg ?_ hint ?_
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun s hs => ?_))
      have hs0 : (0 : ℝ) < s := lt_trans one_pos hs
      simp only [Pi.zero_apply]
      positivity
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun s hs => ?_))
      have hs0 : (0 : ℝ) < s := lt_trans one_pos hs
      have h1 : s ≤ Real.exp (s - 1) := by have := Real.add_one_le_exp (s - 1); linarith
      have h2 : s ^ (n - 1) ≤ Real.exp (((n : ℝ) - 1) * (s - 1)) := by
        calc s ^ (n - 1) ≤ Real.exp (s - 1) ^ (n - 1) := pow_le_pow_left₀ hs0.le h1 _
          _ = Real.exp (((n : ℝ) - 1) * (s - 1)) := by
              rw [← Real.exp_nat_mul, Nat.cast_sub hn]; simp
      calc s ^ (n - 1) * Real.exp (-(α * s))
          ≤ Real.exp (((n : ℝ) - 1) * (s - 1)) * Real.exp (-(α * s)) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = Real.exp (-((n : ℝ) - 1)) * Real.exp (-β * s) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hβ]; ring
  refine hle.trans ?_
  rw [integral_const_mul, integral_exp_mul_Ioi hneg 1]
  have e : Real.exp (-((n : ℝ) - 1)) * (-Real.exp (-β * 1) / -β) = Real.exp (-α) / β := by
    rw [neg_div_neg_eq, ← mul_div_assoc, ← Real.exp_add]
    congr 2; rw [hβ]; ring
  rw [e]
  exact div_le_self (Real.exp_pos _).le hβ1
end Formalism.HermitianLattices.GenusMassVolumes
