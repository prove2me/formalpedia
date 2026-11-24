-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.trace_blkC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:16:01.542322+00:00
-- url     : https://prove2.me/submissions/40dc117b-bb37-48aa-aca0-92e777045271

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open Matrix Complex
variable {ι n : Type} [Fintype ι] [Fintype n]
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution [DecidableEq ι] [DecidableEq n] (N : ι → Matrix n n ℂ) :
    LinearMap.trace ℂ _ (blkC N) = ∑ τ, (N τ).trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis fun _ : ι => Pi.basisFun ℂ n)]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_sigma, blkC, Matrix.mulVec_single_one]
end Formalism.L2.Pj.DatLin
