-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideB.subst_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:33:48.47833+00:00
-- url     : https://prove2.me/submissions/6cad99e5-9db8-4748-a953-4d77357f9647

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideB
import Theorems.Thm_Formalism_L2_Th1_C_USideB_hs_of
import Theorems.Thm_Formalism_L2_Th1_C_USideB_cc_mulBy
import Theorems.Thm_Formalism_L2_Th1_C_USideB_subst_mulBy_l

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
open Formalism.L2.Th1.C.USideB
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.C.USideB
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) (g : PowerSeries K) :
    PowerSeries.subst l (PowerSeries.rescale al g) =
      PowerSeries.subst (mulBy l linv al) (PowerSeries.subst l g) := by
  have hl : PowerSeries.HasSubst l := hs_of h.1
  have hs : PowerSeries.HasSubst (al • PowerSeries.X : PowerSeries K) := hs_of (by simp)
  rw [PowerSeries.subst_comp_subst_apply hl (hs_of (cc_mulBy h al)), subst_mulBy_l h al,
    PowerSeries.rescale_eq_subst, PowerSeries.subst_comp_subst_apply hs hl,
    PowerSeries.subst_smul hl, PowerSeries.subst_X hl, PowerSeries.smul_eq_C_mul]
end Formalism.L2.Th1.C.USideB
