-- Prove2me | solution 1 for Formalism.L2.Th1.B.E2.log_formal_law_three_variables
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:24.987351+00:00
-- url     : https://prove2.me/submissions/f008c1cc-f1c1-4397-b0ce-6ae1eda1b26d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffLawWithInverseThree
import Theorems.Thm_Formalism_L2_Th1_B_E2_cX
import Theorems.Thm_Formalism_L2_Th1_B_E2_constantCoeff_law_first_two_of_three
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_subst_XX
import Theorems.Thm_Formalism_L2_Th1_B_ParE_subst_inVar
import Theorems.Thm_Formalism_L2_Th1_B_ParO_subst_inVar
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.B.E2
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob in3)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_XX subst_zero')
section Div
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
end Div
section Alg
variable {K : Type} [Field K] [CharZero K]
end Alg
section Norm
variable {K : Type} [NormedField K] [CharZero K]
private theorem lawLog_subst_formal_sum_eq_add {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    {u v : MvPowerSeries (Fin 3) K} (hu : MvPowerSeries.constantCoeff u = 0)
    (hv : MvPowerSeries.constantCoeff v = 0) :
    PowerSeries.subst (MvPowerSeries.subst ![u, v] F) l =
      PowerSeries.subst u l + PowerSeries.subst v l := by
  obtain ⟨hF0, -, -, -, hc⟩ := h
  have hF : PowerSeries.subst F l = at1 0 l + at1 1 l := by
    unfold cob at hc
    linear_combination hc
  rw [← psubst_subst l hF0 (hs2 hu hv), hF, MvPowerSeries.subst_add (hs2 hu hv),
    ParO.subst_inVar _ _ (hs2 hu hv), ParO.subst_inVar _ _ (hs2 hu hv)]
  rfl
end Norm
end Formalism.L2.Th1.B.E2
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.E2
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob in3)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_XX subst_zero')
variable {K : Type} [NormedField K] [CharZero K]
namespace Formalism.L2.Th1.B.E2
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) :
    PowerSeries.subst (F3 F) l = at1 0 l + at1 1 l + at1 2 l := by
  unfold F3
  rw [lawLog_subst_formal_sum_eq_add h (constantCoeff_law_first_two_of_three h.1) (cX 2)]
  unfold in3
  rw [lawLog_subst_formal_sum_eq_add h (cX 0) (cX 1)]
  rfl
end Formalism.L2.Th1.B.E2
