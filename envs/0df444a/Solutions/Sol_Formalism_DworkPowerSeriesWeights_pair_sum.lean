-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.pair_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:55:56.591898+00:00
-- url     : https://prove2.me/submissions/9c7acc7e-22f9-4430-a99e-3c5981a32001

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
theorem _root_.solution {K : Type u} [Field K] {R' : Type*} [CommSemiring R'] {n : Type} [Fintype n]
    [DecidableEq n] (c : K →+* R') (Mf Mt : Matrix n n K) (h : Mf * Mt.transpose = 1)
    (Y Y' : n → R') :
    (∑ a, (∑ i, c (Mf i a) * Y i) * (∑ i, c (Mt i a) * Y' i)) = ∑ i, Y i * Y' i := by
  have h1 : ∀ i i', (∑ a, Mf i a * Mt i' a) = if i = i' then 1 else 0 := by
    intro i i'
    have := congrFun (congrFun h i) i'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [Matrix.transpose_apply] using this
  simp only [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have h2 : ∀ i', (∑ a, c (Mf i a) * Y i * (c (Mt i' a) * Y' i')) =
      (if i = i' then 1 else 0) * (Y i * Y' i') := by
    intro i'
    have : (c (∑ a, Mf i a * Mt i' a) : R') = if i = i' then 1 else 0 := by
      rw [h1]
      split_ifs <;> simp
    rw [← this, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul]
    ring
  simp only [h2]
  simp
end Formalism.DworkPowerSeriesWeights
