-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.isUnit_det_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:57.587039+00:00
-- url     : https://prove2.me/submissions/ce01d9e7-33ad-496d-9580-ff79de4dcf0c

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open Formalism.CyclotomicNorms.residueMatrixData
variable {R : Type*} [CommRing R]
namespace Formalism.CyclotomicNorms.residueMatrixData
theorem _root_.solution {a : ℕ} (i j : Fin a) : IsUnit (Matrix.swap R i j).det :=
  isUnit_iff_exists_inv.mpr ⟨(Matrix.swap R i j).det, by rw [← Matrix.det_mul, swap_mul_self, det_one]⟩
end Formalism.CyclotomicNorms.residueMatrixData
