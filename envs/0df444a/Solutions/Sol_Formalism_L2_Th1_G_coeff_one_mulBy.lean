-- Prove2me | solution 1 for Formalism.L2.Th1.G.coeff_one_mulBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:51:14.163948+00:00
-- url     : https://prove2.me/submissions/bd944bf6-8a03-436c-a1bb-67acbe881d9f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Theorems.Thm_Formalism_L2_Th1_G_coeff_one_subst1
import Theorems.Thm_Formalism_L2_Th1_C_Pts_coeff_one_linv


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.G
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) (a : K) :
    PowerSeries.coeff 1 (mulBy l linv a) = a := by
  have h0 : PowerSeries.constantCoeff (PowerSeries.C a * l) = 0 := by rw [map_mul, h.1, mul_zero]
  rw [mulBy, coeff_one_subst1 linv h0, Pts.coeff_one_linv h, PowerSeries.coeff_C_mul, h.2.1, one_mul,
    mul_one]
end Formalism.L2.Th1.G
