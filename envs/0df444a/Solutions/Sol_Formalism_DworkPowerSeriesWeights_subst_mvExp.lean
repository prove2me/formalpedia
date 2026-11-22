-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.subst_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:47.140931+00:00
-- url     : https://prove2.me/submissions/9b52c8bd-1990-4501-a043-cf552ff16fc4

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] [CharZero K] {ι ι' : Type} {a : ι' → MvPowerSeries ι K}
    (hs : MvPowerSeries.HasSubst a) (f : MvPowerSeries ι' K)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := by
  unfold mvExp
  have hf' : MvPowerSeries.HasSubst (fun _ : Unit => f) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hf)
  unfold PowerSeries.subst
  exact MvPowerSeries.subst_comp_subst_apply hf' hs _
end Formalism.DworkPowerSeriesWeights
