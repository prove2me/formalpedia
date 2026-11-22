-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.dirD_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:10:26.371137+00:00
-- url     : https://prove2.me/submissions/ee76a4eb-6056-45d4-b5ed-a9009b5592cf

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer

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
variable {K : Type u} [Field K] {ι : Type} [Fintype ι]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (L : ι → K) (F : MvPowerSeries ι K) :
    dirD L F = ∑ x, MvPowerSeries.C (L x) * MvPowerSeries.pderiv K x F := by
  unfold dirD
  have h := congrFun (map_sum (Derivation.coeFnAddMonoidHom (R := K) (A := MvPowerSeries ι K)
    (M := MvPowerSeries ι K)) (fun x => L x • MvPowerSeries.pderiv K x) Finset.univ) F
  rw [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, MvPowerSeries.smul_eq_C_mul]
end Formalism.DworkPowerSeriesWeights
