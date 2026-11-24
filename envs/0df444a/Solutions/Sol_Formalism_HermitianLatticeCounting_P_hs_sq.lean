-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hs_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:32:20.628802+00:00
-- url     : https://prove2.me/submissions/ae8b0dd7-6d27-4a84-8d34-a9b6b2e34a76

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
theorem _root_.solution {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) : hs Y ^ 2 = ∑ a, ∑ b, ‖Y a b‖ ^ 2 := by
  unfold hs; exact Real.sq_sqrt (by positivity)
end Formalism.HermitianLatticeCounting.P
