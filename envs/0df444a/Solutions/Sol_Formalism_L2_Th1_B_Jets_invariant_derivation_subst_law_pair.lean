-- Prove2me | solution 1 for Formalism.L2.Th1.B.Jets.invariant_derivation_subst_law_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:04.887544+00:00
-- url     : https://prove2.me/submissions/88171430-88e0-4f46-938b-a5655eb0e0f0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
import Theorems.Thm_Formalism_L2_Th1_B_Jets_ccX
import Theorems.Thm_Formalism_L2_Th1_B_Jets_Dj_psubst
import Theorems.Thm_Formalism_L2_Th1_B_Jets_key
import Theorems.Thm_Formalism_L2_Th1_B_Jets_law_subst
import Theorems.Thm_Formalism_L2_Th1_B_Jets_constantCoeff_law_pair
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
variable {K : Type} [Field K] [CharZero K]
variable {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K}
namespace Formalism.L2.Th1.B.Jets
theorem _root_.solution (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (j a b : Fin 3) (hab : a ≠ b) (g : PowerSeries K) :
    Dj l j (PowerSeries.subst (U2 F a b) g) =
      if a = j ∨ b = j then PowerSeries.subst (U2 F a b) (Dinv l g) else 0 := by
  rw [Dj_psubst h1 j g (constantCoeff_law_pair hF a b)]
  have hl : PowerSeries.subst (U2 F a b) l =
      PowerSeries.subst (MvPowerSeries.X a : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X b : MvPowerSeries (Fin 3) K) l :=
    law_subst hF hc (ccX a) (ccX b)
  have ka := key h1 j a
  have kb := key h1 j b
  simp only [pd] at ka kb
  rw [hl]
  simp only [pd, map_add, mul_add]
  rw [ka, kb]
  rcases eq_or_ne a j with ha | ha <;> rcases eq_or_ne b j with hb | hb
  · exact absurd (ha.trans hb.symm) hab
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]
end Formalism.L2.Th1.B.Jets
