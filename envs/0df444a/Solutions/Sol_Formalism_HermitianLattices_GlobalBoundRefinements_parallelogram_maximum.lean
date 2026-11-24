-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.parallelogram_maximum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:46.600134+00:00
-- url     : https://prove2.me/submissions/d9e5f1d2-feb5-4588-82e3-b6cd4496da34

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GlobalBoundRefinements
namespace Formalism.HermitianLattices.GlobalBoundRefinements
theorem _root_.solution : ParallelogramMax := by
  intro T inst1 inst2 M₀ m hpar h0
  have hm : ∀ Q, Q ≠ 0 → m Q = 0 := by
    intro Q hQ
    have hsum : ∑ P : T, (M₀ (P + Q) + M₀ (P - Q) - 2 * M₀ P) = ∑ _P : T, 2 * m Q :=
      Finset.sum_congr rfl (fun P _ => hpar P Q hQ)
    have h1 : ∑ P : T, M₀ (P + Q) = ∑ P : T, M₀ P := Equiv.sum_comp (Equiv.addRight Q) M₀
    have h2 : ∑ P : T, M₀ (P - Q) = ∑ P : T, M₀ P := Equiv.sum_comp (Equiv.subRight Q) M₀
    have e1 : ∑ P : T, (M₀ (P + Q) + M₀ (P - Q) - 2 * M₀ P)
        = ∑ P : T, M₀ (P + Q) + ∑ P : T, M₀ (P - Q) - 2 * ∑ P : T, M₀ P := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    have e2 : ∑ _P : T, 2 * m Q = (Fintype.card T : ℝ) * (2 * m Q) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
    have h3 : (Fintype.card T : ℝ) * (2 * m Q) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h (ne_of_gt hc)
    · linarith
  refine ⟨hm, ?_⟩
  haveI : Nonempty T := ⟨0⟩
  obtain ⟨P, hP⟩ := Finite.exists_max M₀
  have hconst : ∀ R, M₀ R = M₀ P := by
    intro R
    by_cases hQ : R - P = 0
    · rw [sub_eq_zero.mp hQ]
    · have h1 := hpar P (R - P) hQ
      rw [hm _ hQ] at h1
      have e : P + (R - P) = R := by abel
      rw [e] at h1
      exact le_antisymm (hP R) (by linarith [hP (P - (R - P))])
  intro R
  have h00 := hconst 0
  rw [h0] at h00
  rw [hconst R]
  linarith
end Formalism.HermitianLattices.GlobalBoundRefinements
