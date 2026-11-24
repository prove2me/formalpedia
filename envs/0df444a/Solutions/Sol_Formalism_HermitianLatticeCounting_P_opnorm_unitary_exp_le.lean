-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.opnorm_unitary_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:37:27.626331+00:00
-- url     : https://prove2.me/submissions/2c82c4ea-edd3-4bb4-9500-5ae9830f1343

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hsG_exp_sub_one_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_euclNorm_nonneg
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_euclNorm_eq_euclideanSpace_norm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_euclNorm_add_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_euclNorm_mulVec_le_frobenius
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_euclNorm_unitary_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {k : Matrix ι ι ℂ}
    (hk : k ∈ Matrix.unitaryGroup ι ℂ) (Y : Matrix ι ι ℂ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (k * NormedSpace.exp Y))‖
      ≤ Real.exp (hsG Y) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro w
  have e1 : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (k * NormedSpace.exp Y))) w
      = WithLp.toLp 2 ((k * NormedSpace.exp Y) *ᵥ WithLp.ofLp w) := rfl
  have e2 : ‖w‖ = n2G (WithLp.ofLp w) := by rw [euclNorm_eq_euclideanSpace_norm]
  rw [e1, ← euclNorm_eq_euclideanSpace_norm, e2]
  generalize WithLp.ofLp w = v
  rw [← Matrix.mulVec_mulVec, euclNorm_unitary_mulVec hk]
  have e : NormedSpace.exp Y *ᵥ v = v + (NormedSpace.exp Y - 1) *ᵥ v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [e]
  calc n2G (v + (NormedSpace.exp Y - 1) *ᵥ v) ≤ n2G v + n2G ((NormedSpace.exp Y - 1) *ᵥ v) :=
        euclNorm_add_le _ _
    _ ≤ n2G v + (Real.exp (hsG Y) - 1) * n2G v := by
        gcongr
        refine (euclNorm_mulVec_le_frobenius _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (hsG_exp_sub_one_le Y) (euclNorm_nonneg _)
    _ = _ := by ring
end Formalism.HermitianLatticeCounting.P
