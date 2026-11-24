-- Prove2me | solution 1 for Formalism.L2.Th1.B.E2.constantCoeff_law_with_inverse_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:12.291332+00:00
-- url     : https://prove2.me/submissions/c9249040-78d5-47a7-9c5c-b3d9a17123b2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffLawWithInverseThree
import Theorems.Thm_Formalism_L2_Th1_B_E2_cX
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_subst_XX
import Theorems.Thm_Formalism_L2_Th1_B_law_constantCoeff_subst2
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
private theorem constantCoeff_at1_fin_eq_zero {n : ℕ} (k : Fin n) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (at1 k f : MvPowerSeries (Fin n) K) = 0 :=
  (Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) f
    (b := fun _ => (MvPowerSeries.X k : MvPowerSeries (Fin n) K)) (fun _ => by simp)).trans hf
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
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (j k : Fin 3) : MvPowerSeries.constantCoeff (lawDifferenceThree F i j k) = 0 := by
  unfold lawDifferenceThree
  exact law_constantCoeff_subst2 F h.1 _ _ (cX j) (constantCoeff_at1_fin_eq_zero k hi.1)
end Formalism.L2.Th1.B.E2
