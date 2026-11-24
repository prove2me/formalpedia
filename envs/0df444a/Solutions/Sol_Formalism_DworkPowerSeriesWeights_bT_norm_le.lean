-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bT_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:56:01.574938+00:00
-- url     : https://prove2.me/submissions/c4a32e75-efde-4d1e-b362-228263a8a0bf

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {H : Type} {N0 : ℕ}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (x : Bool × H → Matrix (Fin N0) (Fin N0) K) (hx : ∀ τ i a, ‖x τ i a‖ ≤ 1)
    (τ : Bool × H) (i a : Fin N0) : ‖bT x τ i a‖ ≤ 1 := by
  unfold bT
  split_ifs
  · rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul, Matrix.transpose_apply]
    exact mul_le_one₀ (hx _ _ _) (norm_nonneg _) (hx _ _ _)
  · rw [Matrix.one_apply]
    split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights
