-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.constantCoeff_FI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:21:21.452269+00:00
-- url     : https://prove2.me/submissions/16d7b062-751b-474e-aba3-2625613bf78c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
import Theorems.Thm_Formalism_L2_Th1_B_ParO_constantCoeff_inVar
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
    (hi : IsInv l i) : MvPowerSeries.constantCoeff (FI F i) = 0 := by
  have h1 : MvPowerSeries.constantCoeff (Formalism.InvariantFactorPaths.G7.at1 1 i : MvPowerSeries (Fin 2) K) = 0 :=
    constantCoeff_inVar 1 hi.1
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_vec_pair_eq_zero h0 h1))
    (constantCoeff_vec_pair_eq_zero h0 h1) h.1
end Formalism.L2.Th1.B.ParO
