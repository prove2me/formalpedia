-- Prove2me | solution 1 for Formalism.L2.Th1.D.FormalExponential.ip_lgF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:41:40.339495+00:00
-- url     : https://prove2.me/submissions/bad44b75-a41e-4ffb-a4f6-99890b334a84

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExponentialSpecification
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_coeff_one_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_constantCoeff_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_funEq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_subst_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_rescale_lgF


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws (constantCoeff_lgF coeff_one_lgF lgF_subst_inj lgF_funEq map_lgF
  rescale_lgF)
open Formalism.L2.Th1.D.FormalExponential
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.D.FormalExponential
theorem _root_.solution (l : ℕ) (σ : K →+* K) (hl : 2 ≤ l) (hlK : (l : K) ≠ 0) :
    IP l σ (lgF K l : MvPowerSeries Unit K) := by
  refine ⟨constantCoeff_lgF l hl, ?_⟩
  have h1 : MvPowerSeries.map (σ.comp σ) (lgF K l : MvPowerSeries Unit K) = lgF K l :=
    map_lgF (σ.comp σ) l
  have h2 : (lgF K l : MvPowerSeries Unit K) - MvPowerSeries.C ((l : K)⁻¹) *
      frobVar (l ^ 2) (lgF K l : MvPowerSeries Unit K) = (PowerSeries.X : PowerSeries K) := by
    have h := lgF_funEq (K := K) l hl hlK
    rw [PowerSeries.smul_eq_C_mul] at h
    exact h
  rw [h1, h2]
  exact integral_X
end Formalism.L2.Th1.D.FormalExponential
