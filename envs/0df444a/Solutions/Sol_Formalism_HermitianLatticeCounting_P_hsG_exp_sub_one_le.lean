-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hsG_exp_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:12:18.964358+00:00
-- url     : https://prove2.me/submissions/89be0174-8d12-4a2a-af30-c0a2f7034d30

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_exp_sub_one_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hsG_eq_norm

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
open scoped Matrix.Norms.Frobenius
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    hsG (NormedSpace.exp X - 1) ≤ Real.exp (hsG X) - 1 := by
  rw [hsG_eq_norm, hsG_eq_norm]
  exact norm_exp_sub_one_le X
end Formalism.HermitianLatticeCounting.P
