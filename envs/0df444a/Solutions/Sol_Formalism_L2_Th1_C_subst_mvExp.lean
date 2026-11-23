-- Prove2me | solution 1 for Formalism.L2.Th1.C.subst_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:41.153492+00:00
-- url     : https://prove2.me/submissions/b8417026-a9d9-4647-a4e9-9db7f1f2ea6e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Theorems.Thm_Formalism_L2_Th1_C_hasSubst_of_cc

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
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.Th1.C
theorem _root_.solution {f : PowerSeries K} {a : MvPowerSeries σ K}
    (hf : PowerSeries.constantCoeff f = 0) (ha : MvPowerSeries.constantCoeff a = 0) :
    PowerSeries.subst a (mvExp f : PowerSeries K) = mvExp (PowerSeries.subst a f) := by
  unfold mvExp
  exact PowerSeries.subst_comp_subst_apply (hasSubst_of_cc hf) (hasSubst_of_cc ha) _
end Formalism.L2.Th1.C
