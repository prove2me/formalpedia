-- Prove2me | solution 1 for CovecW.herm_bvec_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:03:25.104827+00:00
-- url     : https://prove2.me/submissions/52da0cfa-21eb-4986-855b-477aefe445a5

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianCovectors_HermBvecLeft
import Theorems.Thm_CovecW_mulVec_bvec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CovecW
open Formalism.QuantumDeterminants
namespace CovecW
theorem _root_.solution (k r : ℕ) (H M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x y : Fin (2 * r + k + 1)) :
    herm H (M *ᵥ bvec y) (bvec x) = (H * M) x y := by
  unfold herm
  rw [Matrix.mulVec_mulVec, mulVec_bvec, dotProduct, Finset.sum_eq_single x]
  · simp [bvec]
  · intro l _ hl
    simp [bvec, Pi.single_apply, hl]
  · intro h
    exact absurd (Finset.mem_univ _) h
end CovecW
