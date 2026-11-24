-- Prove2me | solution 1 for Formalism.L2.Th1.C.mvSubst_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:47:24.414688+00:00
-- url     : https://prove2.me/submissions/bdd8d120-177f-4968-909a-bdf29c24ddc0

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
theorem _root_.solution {τ : Type} {f : MvPowerSeries σ K} {a : σ → MvPowerSeries τ K}
    (hf : MvPowerSeries.constantCoeff f = 0) (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := by
  unfold mvExp
  have hs : MvPowerSeries.HasSubst (fun _ : Unit => f) := by
    first
    | exact hasSubst_of_cc hf
    | exact (hasSubst_of_cc hf).const
    | exact PowerSeries.HasSubst.const (hasSubst_of_cc hf)
  first
  | exact MvPowerSeries.subst_comp_subst_apply hs ha _
  | (rw [PowerSeries.subst, PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hs ha])
end Formalism.L2.Th1.C
