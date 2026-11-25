-- Prove2me | solution 1 for Formalism.L2.Th1.C.first_level_from_universal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:21:50.406788+00:00
-- url     : https://prove2.me/submissions/563b5a82-0954-4bb8-9709-6d1035a0f1ce

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Theorems.Thm_Formalism_L2_Th1_C_Dict_substMv_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Dict_subst_biextension_form
import Theorems.Thm_Formalism_L2_Th1_C_Dict_constantCoeff_vec_three_eq_zero
import Theorems.Thm_Formalism_L2_Th1_C_Dict_coboundary_formal_add_biextension
import Theorems.Thm_Formalism_L2_Th1_C_Dict_law_eq
import Theorems.Thm_Formalism_L2_Th1_C_simeq_iff_congruence
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_fadd
import Theorems.Thm_Formalism_L2_Th1_C_lGSubstMv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
namespace Formalism.L2.Th1.C
theorem _root_.solution : FirstLevelFromUniversal := by
  intro K _ _ _ F l linv ph h hL hph hS
  obtain ⟨hF0, hFi, -, -, hc⟩ := hL
  have hF := Dict.law_eq h hF0 hc
  have hFG : FGInt (Formalism.G.unitBall K) l linv := by
    rw [FGInt, ← hF]
    exact hFi
  refine ⟨hF, hFG, ?_⟩
  intro σ x x' y hx hx' hy
  have hLG : LG (Formalism.G.unitBall K) (Formalism.InvariantFactorPaths.G7.d1 F (Formalism.InvariantFactorPaths.G7.cob F ph)) := by
    have := (simeq_iff_congruence K (Fin 3) _ _).1 hS
    rwa [Cong, sub_zero] at this
  have hpt : ∀ s : Fin 3, IsPt (Formalism.G.unitBall K) (![x, x', y] s) := by
    intro s
    fin_cases s
    · exact hx
    · exact hx'
    · exact hy
  have ha := Dict.constantCoeff_vec_three_eq_zero hx.1 hx'.1 hy.1
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have key := lGSubstMv K (Formalism.G.unitBall K) (Fin 3) _ hLG σ ![x, x', y] hpt
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have h2 : MvPowerSeries.constantCoeff (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 2
  rw [hF, Dict.coboundary_formal_add_biextension h ph, MvPowerSeries.subst_sub hs, MvPowerSeries.subst_sub hs,
    Dict.subst_biextension_form h ph (Pts.constantCoeff_fadd h h0 h1) h2 ha, Dict.subst_biextension_form h ph h0 h2 ha,
    Dict.subst_biextension_form h ph h1 h2 ha, Dict.substMv_fadd h h0 h1 ha, MvPowerSeries.subst_X hs,
    MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs] at key
  rw [Cong, ← sub_sub]
  exact key
end Formalism.L2.Th1.C
