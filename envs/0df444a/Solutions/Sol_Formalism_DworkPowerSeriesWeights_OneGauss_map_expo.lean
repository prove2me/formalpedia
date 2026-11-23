-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OneGauss.map_expo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:56.558654+00:00
-- url     : https://prove2.me/submissions/333d5a6e-dc28-409a-9add-de363d4b8310

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
theorem _root_.solution {F : Type} [Field F] (φ : F →+* K) (v : τ → MvPowerSeries ι F)
    (hv : ∀ x, MvPowerSeries.constantCoeff (v x) = 0) (sgn ep : F)
    (be : MvPowerSeries (ZMod 2) F) :
    MvPowerSeries.map φ (expo v sgn ep be) =
      expo (fun x => MvPowerSeries.map φ (v x)) (φ sgn) (φ ep) (MvPowerSeries.map φ be) := by
  unfold expo
  have hs : ∀ (c : F) (f : MvPowerSeries ι F),
      MvPowerSeries.map φ (c • f) = φ c • MvPowerSeries.map φ f := by
    intro c f
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.map_C, MvPowerSeries.smul_eq_C_mul]
  rw [hs, map_sum, map_div₀, map_ofNat]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : ∀ s : ZMod 2,
      MvPowerSeries.constantCoeff ((if s = 0 then (1 : F) else ep) • v x) = 0 :=
    fun s => by
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, hv x, mul_zero]
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero h)]
  congr 1
  funext s
  rw [hs]
  split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights.OneGauss
