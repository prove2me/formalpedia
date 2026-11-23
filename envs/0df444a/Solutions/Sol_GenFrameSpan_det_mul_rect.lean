-- Prove2me | solution 1 for GenFrameSpan.det_mul_rect
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:27.690118+00:00
-- url     : https://prove2.me/submissions/89595039-94ae-4703-8fed-a13196130d1e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GenFrameSpan
namespace GenFrameSpan
theorem _root_.solution {R : Type*} [CommRing R] {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ f : Fin k → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
  simp only [Matrix.det_apply, Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Matrix.submatrix_apply, id, Finset.smul_sum, Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  ring
end GenFrameSpan
