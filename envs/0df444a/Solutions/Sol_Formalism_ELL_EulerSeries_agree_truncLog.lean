-- Prove2me | solution 1 for Formalism.ELL.EulerSeries.agree_truncLog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:02.970819+00:00
-- url     : https://prove2.me/submissions/ad2c5d3f-fc22-4dac-9379-7c6e331dfe4e

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ConstantCoeffLogOnePlus
import Theorems.Thm_Formalism_ELL_EulerSeries_coeff_pow_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.EulerSeries
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [CharZero K] {σ : Type} [DecidableEq σ]
namespace Formalism.ELL.EulerSeries
theorem _root_.solution {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (N : ℕ) : Agree N (logOnePlus f) (truncLog N f) := by
  intro d hd
  rw [logOnePlus, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    truncLog, map_sum]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N) ?_]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul]
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hn
    rw [coeff_pow_eq_zero hf n d (by omega), smul_zero]
end Formalism.ELL.EulerSeries
