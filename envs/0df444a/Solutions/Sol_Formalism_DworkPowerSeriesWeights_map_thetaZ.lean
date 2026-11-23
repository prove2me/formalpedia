-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.map_thetaZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:44.927356+00:00
-- url     : https://prove2.me/submissions/0d6ef4fa-3e1c-4c2f-b059-0c8333ef2914

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_linSub
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_bSum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_linSub
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_bSum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_mvExp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_idM

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
variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)
  {d N0 N1 : ℕ} [NeZero d] {ι : Type} [Fintype ι]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) F)
    (U : MvPowerSeries (ZV d N0 N1) F) (ε : F) (be : MvPowerSeries (ZMod d) F)
    (hg : ∀ y, MvPowerSeries.constantCoeff (g y) = 0) (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.map φ (thetaZ g U ε be) =
      thetaZ (fun y => MvPowerSeries.map φ (g y)) (MvPowerSeries.map φ U) (φ ε)
        (MvPowerSeries.map φ be) := by
  have hsm : ∀ (c : F) (f : MvPowerSeries (ZV d N0 N1) F),
      MvPowerSeries.map φ (c • f) = φ c • MvPowerSeries.map φ f := by
    intro c f
    ext n
    simp [MvPowerSeries.coeff_map]
  unfold thetaZ
  rw [map_mul,
    MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun z => constantCoeff_linSub idM z),
    MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hg),
    map_mvExp φ _ (by rw [MvPowerSeries.constantCoeff_smul, constantCoeff_bSum idM be hbe, smul_zero]),
    hsm, map_bSum]
  simp only [map_linSub, map_idM]
end Formalism.DworkPowerSeriesWeights
