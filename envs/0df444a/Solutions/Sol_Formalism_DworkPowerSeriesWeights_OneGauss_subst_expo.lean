-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OneGauss.subst_expo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:48.691807+00:00
-- url     : https://prove2.me/submissions/78cb14a1-5021-4f91-8f69-e58a09af82c3

import Definitions.Def_Formalism_GaussJetBounds_StatementU
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_cc_smul
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights.OneGauss
variable {K : Type} [Field K] {τ ι : Type} [Fintype τ]
namespace Formalism.DworkPowerSeriesWeights.OneGauss
theorem _root_.solution {ι' : Type} {a : ι → MvPowerSeries ι' K} (hs : MvPowerSeries.HasSubst a)
    (v : τ → MvPowerSeries ι K) (hv : ∀ x, MvPowerSeries.constantCoeff (v x) = 0)
    (sgn ep : K) (be : MvPowerSeries (ZMod 2) K) :
    MvPowerSeries.subst a (expo v sgn ep be) =
      expo (fun x => MvPowerSeries.subst a (v x)) sgn ep be := by
  unfold expo
  rw [MvPowerSeries.subst_smul hs, ← MvPowerSeries.substAlgHom_apply hs, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : ∀ s : ZMod 2,
      MvPowerSeries.constantCoeff ((if s = 0 then (1 : K) else ep) • v x) = 0 :=
    fun s => cc_smul _ (hv x)
  rw [MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero h) hs]
  congr 1
  funext s
  rw [MvPowerSeries.subst_smul hs]
end Formalism.DworkPowerSeriesWeights.OneGauss
