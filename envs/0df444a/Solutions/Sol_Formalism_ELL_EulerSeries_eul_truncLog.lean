-- Prove2me | solution 1 for Formalism.ELL.EulerSeries.eul_truncLog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:40.692153+00:00
-- url     : https://prove2.me/submissions/bb46e549-b01b-4a32-8140-401ab427ae2e

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ConstantCoeffLogOnePlus
import Theorems.Thm_Formalism_ELL_EulerSeries_eul_apply
import Theorems.Thm_Formalism_ELL_EulerSeries_coeff_log_succ_mul

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
theorem _root_.solution (f : MvPowerSeries σ K) (M : ℕ) :
    eulFun (truncLog (M + 1) f) = (∑ k ∈ Finset.range M, (-f) ^ k) * eulFun f := by
  have h0 : PowerSeries.coeff 0 (PowerSeries.log K) = 0 := by simp
  rw [← eul_apply, truncLog, map_sum, Finset.sum_range_succ', h0, zero_smul, map_zero,
    add_zero, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Derivation.map_smul, Derivation.leibniz_pow, Nat.add_sub_cancel, Algebra.smul_def,
    nsmul_eq_mul, smul_eq_mul, eul_apply, neg_pow]
  have h1 : algebraMap K (MvPowerSeries σ K) (PowerSeries.coeff (k + 1) (PowerSeries.log K)) *
      ((k + 1 : ℕ) : MvPowerSeries σ K) = (-1) ^ k := by
    rw [← map_natCast (algebraMap K (MvPowerSeries σ K)), ← map_mul, coeff_log_succ_mul,
      map_pow, map_neg, map_one]
  linear_combination (f ^ k * eulFun f) * h1
end Formalism.ELL.EulerSeries
