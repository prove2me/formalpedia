-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.traceDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:13.818548+00:00
-- url     : https://prove2.me/submissions/3b6061b6-ed68-4d6e-ad69-f81808354b55

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
namespace Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
theorem _root_.solution : TraceDual := by
  intro F L ι _ _ _ _ _ _ _ b σ τ
  classical
  let A : Matrix ι (L ≃ₐ[F] L) L := fun r ρ =>
    ρ ((Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b r)
  let B : Matrix (L ≃ₐ[F] L) ι L := fun ρ r => ρ (b r)
  have hAB : A * B = 1 := by
    ext r s
    rw [Matrix.mul_apply]
    have e : ∑ ρ : L ≃ₐ[F] L, A r ρ * B ρ s = algebraMap F L (Algebra.trace F L
        ((Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b r * b s)) := by
      rw [trace_eq_sum_automorphisms]
      exact Finset.sum_congr rfl fun ρ _ => (map_mul ρ _ _).symm
    rw [e, ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_dualBasis_left, Matrix.one_apply]
    by_cases h : r = s
    · rw [if_pos h, if_pos h.symm, map_one]
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  have e : ι ≃ (L ≃ₐ[F] L) := Fintype.equivOfCardEq (by
    rw [← Module.finrank_eq_card_basis b, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card])
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hAB
  have key : ∑ r, σ ((Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b r) * τ (b r) =
      (1 : Matrix (L ≃ₐ[F] L) (L ≃ₐ[F] L) L) τ σ := by
    rw [← hBA, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  rw [key]
  exact ⟨fun h => by rw [h, Matrix.one_apply_eq], fun h => Matrix.one_apply_ne (Ne.symm h)⟩
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
