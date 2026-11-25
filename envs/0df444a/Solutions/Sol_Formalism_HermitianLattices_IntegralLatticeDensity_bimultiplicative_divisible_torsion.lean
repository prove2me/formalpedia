-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.bimultiplicative_divisible_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:15:37.178326+00:00
-- url     : https://prove2.me/submissions/4380c916-f626-4d5a-9b6d-4eff86b47225

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity
open Finset Formalism.LogVandermondeBounds.TaylorLogMetric
namespace Formalism.HermitianLattices.IntegralLatticeDensity
theorem _root_.solution : BimultDivisibleTorsion := by
  unfold BimultDivisibleTorsion
  intro B H _ _ htor hdiv
  refine ⟨fun z hz1 hz2 a b => ?_, fun c hc hneg a => ?_⟩
  · have hz0 : z 0 b = 1 := by
      have := hz1 0 0 b
      rw [add_zero] at this
      exact mul_left_cancel (this.symm.trans (mul_one _).symm)
    obtain ⟨n, hn, hnb⟩ := htor b
    obtain ⟨a', rfl⟩ := hdiv a n hn
    have hz0' : z a' 0 = 1 := by
      have := hz2 a' 0 0
      rw [add_zero] at this
      exact mul_left_cancel (this.symm.trans (mul_one _).symm)
    have h1 : ∀ k : ℕ, z (k • a') b = z a' b ^ k := by
      intro k
      induction k with
      | zero => rw [zero_smul, pow_zero, hz0]
      | succ k ih => rw [succ_nsmul, hz1, ih, pow_succ]
    have h2 : ∀ k : ℕ, z a' (k • b) = z a' b ^ k := by
      intro k
      induction k with
      | zero => rw [zero_smul, pow_zero, hz0']
      | succ k ih => rw [succ_nsmul, hz2, ih, pow_succ]
    rw [h1, ← h2, hnb, hz0']
  · have hc0 : c 0 = 1 := by
      have := hc 0 0
      rw [add_zero] at this
      exact mul_left_cancel (this.symm.trans (mul_one _).symm)
    have hsq : ∀ x, c x * c x = 1 := by
      intro x
      have := hc x (-x)
      rw [add_neg_cancel, hc0, hneg] at this
      exact this.symm
    obtain ⟨a', rfl⟩ := hdiv a 2 (by norm_num)
    rw [two_nsmul, hc, hsq]
end Formalism.HermitianLattices.IntegralLatticeDensity
