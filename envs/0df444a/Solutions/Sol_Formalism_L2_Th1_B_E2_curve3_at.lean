-- Prove2me | solution 1 for Formalism.L2.Th1.B.E2.curve3_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:03:04.115808+00:00
-- url     : https://prove2.me/submissions/7cd70907-2374-480c-bec2-8468a404fabd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffLawWithInverseThree
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
private theorem at1_C_eq_C {ι : Type} (x : ι) (c : K) :
    at1 x (PowerSeries.C c) = (MvPowerSeries.C c : MvPowerSeries ι K) := by
  have hx : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) := PowerSeries.HasSubst.X x
  have e := (PowerSeries.substAlgHom hx).commutes c
  rw [PowerSeries.coe_substAlgHom] at e
  exact e
end Alg
section Norm
variable {K : Type} [NormedField K] [CharZero K]
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
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.E2
theorem _root_.solution {ι : Type} {l P ep : PowerSeries K} {a1 a3 : K}
    (hl : PowerSeries.constantCoeff l = 0)
    (h : PowerSeries.X ^ 3 * (-2 + l ^ 3 * PowerSeries.subst l (PowerSeries.derivative K P)) =
      l ^ 3 * (-2 * ep + PowerSeries.C a1 * PowerSeries.X * ep +
        PowerSeries.C a3 * PowerSeries.X ^ 3)) (x : ι) :
    MvPowerSeries.X x ^ 3 * (-2 + at1 x l ^ 3 * PowerSeries.subst (at1 x l) (dz P)) =
      at1 x l ^ 3 * (-2 * at1 x ep + MvPowerSeries.C a1 * MvPowerSeries.X x * at1 x ep +
        MvPowerSeries.C a3 * MvPowerSeries.X x ^ 3) := by
  have hx : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) := PowerSeries.HasSubst.X x
  have e := congrArg (PowerSeries.substAlgHom hx) h
  simp only [map_mul, map_add, map_pow, map_neg, map_ofNat, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hx] at e
  have e1 : ∀ f : PowerSeries K,
      PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries ι K) f = at1 x f := fun f => rfl
  simp only [e1, at1_C_eq_C, ParE.subst_inVar x _ hl] at e
  exact e
end Formalism.L2.Th1.B.E2
