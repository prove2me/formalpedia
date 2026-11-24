-- Prove2me | solution 1 for Formalism.G0.DetDividesP.degreeOf_det_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:22.808873+00:00
-- url     : https://prove2.me/submissions/55295653-d593-411b-abf7-ef2e97a95793

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution {σ : Type} (M : Matrix (Fin r) (Fin r) (MvPolynomial σ K)) (x : σ)
    (h : ∀ i j, degreeOf x (M i j) = 0) : degreeOf x M.det = 0 := by
  rw [Matrix.det_apply]
  apply Nat.eq_zero_of_le_zero
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun σ' _ => ?_)
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : K →+* MvPolynomial σ K)]
  refine (degreeOf_C_mul_le _ _ _).trans ?_
  refine (degreeOf_prod_le _ _ _).trans ?_
  simp [h]
end Formalism.G0.DetDividesP
