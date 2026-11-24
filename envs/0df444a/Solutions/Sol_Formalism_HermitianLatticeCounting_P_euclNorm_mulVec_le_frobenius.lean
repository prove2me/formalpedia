-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.euclNorm_mulVec_le_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:14:05.723701+00:00
-- url     : https://prove2.me/submissions/e17d6986-e5af-4b04-a3c3-60b9bcee9ab7

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hsG_nonneg
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hsG_sq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_euclNorm_nonneg
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_euclNorm_sq_eq_sum_sq

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    n2G (A *ᵥ v) ≤ hsG A * n2G v := by
  apply (sq_le_sq₀ (euclNorm_nonneg _) (mul_nonneg (hsG_nonneg _) (euclNorm_nonneg _))).mp
  rw [mul_pow, euclNorm_sq_eq_sum_sq, hsG_sq, euclNorm_sq_eq_sum_sq, Finset.sum_mul]
  apply Finset.sum_le_sum; intro a _
  calc ‖(A *ᵥ v) a‖ ^ 2 ≤ (∑ b, ‖A a b‖ * ‖v b‖) ^ 2 := by
        gcongr
        rw [Matrix.mulVec, dotProduct]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp_rw [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
end Formalism.HermitianLatticeCounting.P
