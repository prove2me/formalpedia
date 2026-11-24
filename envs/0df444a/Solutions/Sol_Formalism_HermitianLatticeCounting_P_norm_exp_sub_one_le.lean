-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.norm_exp_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:52:06.587875+00:00
-- url     : https://prove2.me/submissions/7e146688-5569-44ca-b8f9-53717cbc0b13

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h1
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open scoped Matrix.Norms.Frobenius
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (x : A) :
    ‖NormedSpace.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have h1 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • x ^ n) (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x
  have h2 : HasSum (fun n : ℕ => ‖x‖ ^ n / (n.factorial : ℝ)) (Real.exp ‖x‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ‖x‖
  have h1' := (hasSum_nat_add_iff' 1).mpr h1
  have h2' := (hasSum_nat_add_iff' 1).mpr h2
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    div_one] at h1' h2'
  refine h1'.norm_le_of_bounded h2' (fun n => ?_)
  rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  gcongr
  exact norm_pow_le' x (Nat.succ_pos n)
end Formalism.HermitianLatticeCounting.P
