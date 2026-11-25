-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.parallelogram_law_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:04:47.312404+00:00
-- url     : https://prove2.me/submissions/d91f95a8-4e65-4961-9630-f542836093ad

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
theorem _root_.solution : ParallelogramZero := by
  unfold ParallelogramZero
  intro T _ _ m h h0 Q
  by_cases hQ : Q = 0
  · rw [hQ, h0]
  have hsum := Finset.sum_congr rfl (fun P (_ : P ∈ (univ : Finset T)) => h P Q hQ)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have e1 : ∑ P, m (P + Q) = ∑ P, m P := Fintype.sum_equiv (Equiv.addRight Q) _ _ (fun _ => rfl)
  have e2 : ∑ P, m (P - Q) = ∑ P, m P := Fintype.sum_equiv (Equiv.subRight Q) _ _ (fun _ => rfl)
  have e3 : ∑ P, 2 * m P = 2 * ∑ P, m P := by rw [Finset.mul_sum]
  rw [e1, e2, e3] at hsum
  have hc : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  have h4 : (Fintype.card T : ℝ) * (2 * m Q) = 0 := by linarith
  rcases mul_eq_zero.1 h4 with h5 | h5
  · linarith
  · linarith
end Formalism.HermitianLattices.IntegralLatticeDensity
