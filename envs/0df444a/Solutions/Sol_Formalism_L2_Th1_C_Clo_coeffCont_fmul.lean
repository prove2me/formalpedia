-- Prove2me | solution 1 for Formalism.L2.Th1.C.Clo.coeffCont_fmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:06.290806+00:00
-- url     : https://prove2.me/submissions/70774560-14e3-41b6-931b-23ed0b06cd5b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_const
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_C_mul
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_Clo_cc_C_mul
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Clo
variable {K : Type} [Field K] {σ : Type}
variable [TopologicalSpace K] [IsTopologicalRing K] {T : Type} [TopologicalSpace T]
namespace Formalism.L2.Th1.C.Clo
theorem _root_.solution {l : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0)
    (linv : PowerSeries K) {c : T → K} (hc : Continuous c) {y : MvPowerSeries σ K}
    (hy : MvPowerSeries.constantCoeff y = 0) : CoeffCont fun t => fmul l linv (c t) y :=
  (CoeffCont.C_mul hc (CoeffCont.const _)).subst
    (fun t => cc_C_mul (Pts.constantCoeff_subst hy hl) (c t)) linv
end Formalism.L2.Th1.C.Clo
