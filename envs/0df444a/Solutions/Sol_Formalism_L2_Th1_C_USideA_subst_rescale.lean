-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideA.subst_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:22:00.363898+00:00
-- url     : https://prove2.me/submissions/c08692a0-d5a6-41c5-8b89-f05a6b0a98aa

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideA
import Theorems.Thm_Formalism_L2_Th1_C_USideA_hs_of
import Theorems.Thm_Formalism_L2_Th1_C_USideA_cc_mulBy
import Theorems.Thm_Formalism_L2_Th1_C_USideA_subst_mulBy_l

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
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.USideA
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.C.USideA
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) (g : PowerSeries K) :
    PowerSeries.subst l (PowerSeries.rescale al g) =
      PowerSeries.subst (mulBy l linv al) (PowerSeries.subst l g) := by
  have hl : PowerSeries.HasSubst l := hs_of h.1
  have hm : PowerSeries.HasSubst (mulBy l linv al) := hs_of (cc_mulBy h al)
  have hX : PowerSeries.HasSubst (PowerSeries.C al * PowerSeries.X : PowerSeries K) := hs_of (by simp)
  have hC : PowerSeries.subst l (PowerSeries.C al) = PowerSeries.C al := PowerSeries.subst_C al
  rw [PowerSeries.subst_comp_subst_apply hl hm, subst_mulBy_l h, PowerSeries.rescale_eq_subst,
    PowerSeries.smul_eq_C_mul, PowerSeries.subst_comp_subst_apply hX hl,
    ← PowerSeries.coe_substAlgHom hl, map_mul, PowerSeries.coe_substAlgHom, hC,
    PowerSeries.subst_X hl]
end Formalism.L2.Th1.C.USideA
