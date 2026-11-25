-- Prove2me | solution 1 for Formalism.L2.Th1.H.FormalGroupLawNegation.subst_single_var
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:22:14.68966+00:00
-- url     : https://prove2.me/submissions/91cd7a69-e3ba-41e3-af33-15461fa8559b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_SubstSingleVar
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_substMv_subst


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.C (IsLogPair)
open Formalism.L2.Th1.E (tensor4 matCoord thetaProd)
open Formalism.L2.Th1.H.FormalGroupLawNegation
variable {K : Type} [Field K] {n : Type} [Fintype n]
namespace Formalism.L2.Th1.H.FormalGroupLawNegation
theorem _root_.solution {σ ρ : Type} [Finite σ] (s : σ) (f : PowerSeries K) {φ : σ → MvPowerSeries ρ K}
    (hφ : ∀ s, MvPowerSeries.constantCoeff (φ s) = 0) :
    MvPowerSeries.subst φ (at1 s f) = PowerSeries.subst (φ s) f := by
  unfold at1
  rw [Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X s) hφ,
    MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hφ)]
end Formalism.L2.Th1.H.FormalGroupLawNegation
