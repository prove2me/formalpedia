-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hs_unitary_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:55:43.331823+00:00
-- url     : https://prove2.me/submissions/51059650-3224-40a8-94c1-69e561e2f0a5

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hs_of_gram_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_unitary_left

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
theorem _root_.solution {N : ℕ} {k : Matrix (Fin N) (Fin N) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin N) ℂ) (Y : Matrix (Fin N) (Fin N) ℂ) : hs (k * Y) = hs Y := by
  apply hs_of_gram_eq
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ, unitary_left hk,
    Matrix.one_mul]
end Formalism.HermitianLatticeCounting.P
