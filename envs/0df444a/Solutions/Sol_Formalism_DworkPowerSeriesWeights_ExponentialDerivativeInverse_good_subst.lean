-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.good_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:13.073834+00:00
-- url     : https://prove2.me/submissions/f09fb55c-a840-43cb-ae20-428be096c293

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_inSub_subst
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ExponentialDerivativeInverse_congW_subst

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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
variable {K : Type u} [NormedField K] {d : ℕ}
namespace Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
theorem _root_.solution [NeZero d] {K0 : Subfield K} {l : ℕ} {N : ℤ} {be : MvPowerSeries (ZMod d) K}
    (hK0 : InSub K0 be) (hcc : MvPowerSeries.constantCoeff be = 0) (hcb : CongW N (lw l) be)
    {a : ZMod d → MvPowerSeries (V2 d) K} (ha : Fam K0 l a) :
    Good K0 N (fun x : V2 d => lw l x.2) (MvPowerSeries.subst a be) :=
  ⟨MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (ha s).1) (fun s => (ha s).1) hcc,
    inSub_subst (fun s => (ha s).1) (fun s => (ha s).2.1) hK0,
    congW_subst (fun s => (ha s).1) (fun s => (ha s).2.2) hcb⟩
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
