-- Prove2me | solution 1 for Formalism.L2.Th1.C.rescale_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:47.224404+00:00
-- url     : https://prove2.me/submissions/bbd3a2d8-1e1d-4a4b-aef6-4c84fff8766f

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
theorem _root_.solution {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) (c : K) :
    PowerSeries.rescale c (mvExp f : PowerSeries K) = mvExp (PowerSeries.rescale c f) := by
  unfold mvExp
  have hX : PowerSeries.HasSubst (c • PowerSeries.X : PowerSeries K) :=
    hasSubst_of_cc (by
      first
      | (simp; done)
      | (simp only [map_smul, smul_eq_zero]; right; exact PowerSeries.constantCoeff_X)
      | (simp [PowerSeries.X]; done))
  rw [PowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst,
    PowerSeries.subst_comp_subst_apply (hasSubst_of_cc hf) hX]
end Formalism.L2.Th1.C
