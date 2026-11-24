-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sum_block_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:55:59.989539+00:00
-- url     : https://prove2.me/submissions/9cfa93e4-d1ce-442a-a309-fa810d9751d3

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {T : Type} [Fintype T] [DecidableEq T] {N0 N1 : ℕ} {M : Type*}
    [AddCommMonoid M] (s : T) (b : Fin N1) (f : T × Fin N0 × Fin N1 → M)
    (hf : ∀ y, ¬ (y.1 = s ∧ y.2.2 = b) → f y = 0) :
    ∑ y, f y = ∑ k, f (s, k, b) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single b]
    · intro b' _ hb'
      exact hf _ fun h => hb' h.2
    · intro h
      exact absurd (Finset.mem_univ b) h
  · intro s' _ hs'
    exact Finset.sum_eq_zero fun y _ => hf _ fun h => hs' h.1
  · intro h
    exact absurd (Finset.mem_univ s) h
end Formalism.DworkPowerSeriesWeights
