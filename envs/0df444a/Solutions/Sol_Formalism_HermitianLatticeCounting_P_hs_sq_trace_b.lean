-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hs_sq_trace_b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:41.275827+00:00
-- url     : https://prove2.me/submissions/5fa9ea30-8877-4ecc-a211-632f416825c6

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) :
    ((∑ a, ∑ b, ‖Y a b‖ ^ 2 : ℝ) : ℂ) = (Yᴴ * Y).trace := by
  simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show star (Y b a) = (starRingEnd ℂ) (Y b a) from rfl, Complex.conj_mul']
end Formalism.HermitianLatticeCounting.P
