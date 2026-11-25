-- Prove2me | solution 1 for Formalism.L2.Th1.B.Mul.mulN_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:58:24.770522+00:00
-- url     : https://prove2.me/submissions/ee9b5806-0216-4277-8c6e-6952778b91b2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_MultiplicationBiadditiveHolds
import Theorems.Thm_Formalism_L2_Th1_B_Mul_mulN_spec
import Theorems.Thm_Formalism_L2_Th1_B_Mul_mulN_eq
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Mul
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_zero')
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.L2.Th1.B.Mul
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) (n m : ℤ) :
    MvPowerSeries.subst ![mulN h n, mulN h m] F = mulN h (n + m) :=
  have e := isMul_add h (mulN_spec h n) (mulN_spec h m)
  mulN_eq h (n + m) _ e.1 e.2.2
end Formalism.L2.Th1.B.Mul
