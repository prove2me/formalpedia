-- Prove2me | solution 1 for Formalism.CohomologicalDescent.lw_det_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:41:35.141087+00:00
-- url     : https://prove2.me/submissions/0f050428-6cfe-4f25-b065-b41017e105b7

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLW
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MinorValuationBoundHolds
import Theorems.Thm_Formalism_CohomologicalDescent_lw_det_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent
theorem _root_.solution {R m : Type*} [CommRing R] [DecidableEq m] [Fintype m]
    (M : Matrix m m R) (b : m → ℕ) (hM : M.BlockTriangular b) (hb : Function.Injective b) :
    M.det = ∏ i, M i i := by
  rw [Matrix.BlockTriangular.det hM, Finset.prod_image]
  · exact Finset.prod_congr rfl (fun i _ => lw_det_block M b i (fun j hj => hb hj))
  · intro x _ y _ hxy
    exact hb hxy
end Formalism.CohomologicalDescent
