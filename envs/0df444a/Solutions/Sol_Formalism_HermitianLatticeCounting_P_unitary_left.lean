-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.unitary_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:32:14.80546+00:00
-- url     : https://prove2.me/submissions/b1d20857-0146-415e-971c-390cece19ab9

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
theorem _root_.solution {N : ℕ} {k : Matrix (Fin N) (Fin N) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    kᴴ * k = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp hk
  rwa [Matrix.star_eq_conjTranspose] at this
end Formalism.HermitianLatticeCounting.P
