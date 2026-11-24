-- Prove2me | solution 1 for Formalism.L2.Th1.C.adjoint_universal_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:47:17.757896+00:00
-- url     : https://prove2.me/submissions/2174c108-4156-4faa-b39f-14502d9cb5f6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Theorems.Thm_Formalism_L2_Th1_C_Dict_subst_cob
import Theorems.Thm_Formalism_L2_Th1_C_Dict_law_eq
import Theorems.Thm_Formalism_L2_Th1_C_simeq_iff_congruence
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_fmul
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fmul_eq_subst_mulBy
import Theorems.Thm_Formalism_L2_Th1_C_Pts_intMv_X


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
theorem _root_.solution : AdjUniversal := by
  intro K _ _ _ F l linv ph a b h hL hph ha hb hA
  obtain ⟨hF0, hFi, -, -, hc⟩ := hL
  have hF := Dict.law_eq h hF0 hc
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have p0 : IsPt (Formalism.G.unitBall K) (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    ⟨h0, Pts.intMv_X 0⟩
  have p1 : IsPt (Formalism.G.unitBall K) (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    ⟨h1, Pts.intMv_X 1⟩
  have key := hA (Fin 2) _ _ p0 p1
  rw [simeq_iff_congruence K (Fin 2), hF, Formalism.InvariantFactorPaths.G7.at1, Formalism.InvariantFactorPaths.G7.at1,
    ← Pts.fmul_eq_subst_mulBy h a h0, ← Pts.fmul_eq_subst_mulBy h b h1,
    Dict.subst_cob h ph (Pts.constantCoeff_fmul h a h0) h1,
    Dict.subst_cob h ph h0 (Pts.constantCoeff_fmul h b h1)]
  exact key
end Formalism.L2.Th1.C
