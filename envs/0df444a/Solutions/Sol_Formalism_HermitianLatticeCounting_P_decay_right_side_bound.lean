-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.decay_right_side_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:28:43.785054+00:00
-- url     : https://prove2.me/submissions/a466134b-54e2-48f3-80a7-cb7a2a4120ae

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_conjugation_invariant_measure
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_decay_assembly_holds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gap_sum_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_resolution_norm_bound
import Theorems.Thm_Formalism_NuclearRankWeightBounds_Top_decay


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
theorem _root_.solution : DecayRightSide :=
  decay_assembly_holds Formalism.NuclearRankWeightBounds.Top.decay resolution_norm_bound conjugation_invariant_measure gap_sum_bound
end Formalism.HermitianLatticeCounting.P
