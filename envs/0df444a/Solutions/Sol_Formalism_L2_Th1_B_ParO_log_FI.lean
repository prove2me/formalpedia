-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.log_FI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:21:12.330691+00:00
-- url     : https://prove2.me/submissions/052317bd-715f-472f-b7e1-56ad649086cc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
import Theorems.Thm_Formalism_L2_Th1_B_ParO_subst_inVar
import Theorems.Thm_Formalism_L2_Th1_B_ParO_constantCoeff_inVar
import Theorems.Thm_Formalism_L2_Th1_B_ParO_psubst_neg
import Theorems.Thm_Formalism_L2_Th1_B_ParO_log_law
import Theorems.Thm_Formalism_L2_Th1_B_psubst_msubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.B.ParO
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
section Alg
variable {K : Type} [Field K] [CharZero K]
private theorem constantCoeff_vec_pair_eq_zero {ι : Type} {a b : MvPowerSeries ι K}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    ∀ s : Fin 2, MvPowerSeries.constantCoeff (![a, b] s) = 0 :=
  Fin.forall_fin_two.mpr ⟨ha, hb⟩
end Alg
section Norm
variable {K : Type} [NormedField K] [CharZero K]
end Norm
section Alg2
variable {K : Type} [Field K] [CharZero K]
end Alg2
end Formalism.L2.Th1.B.ParO
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParO
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
variable {K : Type} [NormedField K] [CharZero K]
namespace Formalism.L2.Th1.B.ParO
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) : PowerSeries.subst (FI F i) l = at1 0 l - at1 1 l := by
  have h1 : MvPowerSeries.constantCoeff (Formalism.InvariantFactorPaths.G7.at1 1 i : MvPowerSeries (Fin 2) K) = 0 :=
    constantCoeff_inVar 1 hi.1
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hX1c : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hb : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), Formalism.InvariantFactorPaths.G7.at1 1 i] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_vec_pair_eq_zero h0 h1)
  have hiS := PowerSeries.HasSubst.of_constantCoeff_zero' hi.1
  have hX1 : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := PowerSeries.HasSubst.X 1
  rw [Formalism.L2.Th1.B.FI, ← Formalism.L2.Th1.B.psubst_msubst l h.1 hb, log_law h, MvPowerSeries.subst_add hb,
    subst_inVar l 0 hb, subst_inVar l 1 hb]
  show PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l
      + PowerSeries.subst (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) i) l
      = PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l
        - PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l
  rw [← PowerSeries.subst_comp_subst_apply hiS hX1, hi.2.2, psubst_neg hX1c l, sub_eq_add_neg]
end Formalism.L2.Th1.B.ParO
