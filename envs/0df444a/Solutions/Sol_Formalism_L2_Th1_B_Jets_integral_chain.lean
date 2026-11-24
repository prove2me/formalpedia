-- Prove2me | solution 1 for Formalism.L2.Th1.B.Jets.integral_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:28:48.89764+00:00
-- url     : https://prove2.me/submissions/51ac3809-28f7-40a0-a70d-094230dcc7d0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
import Theorems.Thm_Formalism_L2_Th1_B_Jets_integral_pd
import Theorems.Thm_Formalism_L2_Th1_B_Jets_integral_Dj
import Theorems.Thm_Formalism_L2_Th1_B_Jets_integral_pd_of_simeq
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Jets
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3)
open Formalism.G.LogP (hs2 psubst_subst constantCoeff_subst_of_zero psubst_injective)
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.L2.Th1.B.Jets
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    {T : MvPowerSeries (Fin 3) K} (hT : Simeq T 0) (k : ℕ) :
    Integral ((Dj l 0)^[k] (Dj l 0 (Dj l 1 (Dj l 2 T)))) := by
  have step : ∀ (j : Fin 3) (g : MvPowerSeries (Fin 3) K), Integral g → Integral (Dj l j g) :=
    fun j g hg => integral_Dj h j (integral_pd j hg)
  have base : Integral (Dj l 0 (Dj l 1 (Dj l 2 T))) :=
    step 0 _ (step 1 _ (integral_Dj h 2 (integral_pd_of_simeq hT 2)))
  induction k with
  | zero => exact base
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact step 0 _ ih
end Formalism.L2.Th1.B.Jets
