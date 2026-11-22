-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.sum_range_ite_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:06.102521+00:00
-- url     : https://prove2.me/submissions/fa07887d-3c94-4234-80c1-a6fd8d02c936

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA

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
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {M : Type} [AddCommMonoid M] (N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (c : ℕ → M) (j0 : ℕ) (h0 : j0 < N) (hP : P j0) (hu : ∀ j, P j → j = j0) :
    (∑ j ∈ range N, if P j then c j else 0) = c j0 := by
  rw [Finset.sum_eq_single j0]
  · rw [if_pos hP]
  · intro b _ hb
    rw [if_neg (fun h => hb (hu b h))]
  · intro h
    exact absurd (Finset.mem_range.mpr h0) h
end Formalism.InvariantFactorPaths.G7
