-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hsG_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:32:18.603247+00:00
-- url     : https://prove2.me/submissions/fddd45e2-e38c-4c18-aa8e-5d9ad4fb9fe4

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) : 0 ≤ hsG Y := Real.sqrt_nonneg _
end Formalism.HermitianLatticeCounting.P
