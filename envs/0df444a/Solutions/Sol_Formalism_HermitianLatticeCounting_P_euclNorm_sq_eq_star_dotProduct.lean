-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.euclNorm_sq_eq_star_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:56:16.831005+00:00
-- url     : https://prove2.me/submissions/3727e699-aaf8-4a46-87c3-64bbb4f3b3de

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) : ((n2G v ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v := by
  rw [euclNorm_sq_eq_sum_sq, dotProduct]
  push_cast
  apply Finset.sum_congr rfl; intro i _
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
end Formalism.HermitianLatticeCounting.P
