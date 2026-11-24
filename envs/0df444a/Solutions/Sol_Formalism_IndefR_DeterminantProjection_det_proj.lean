-- Prove2me | solution 1 for Formalism.IndefR.DeterminantProjection.det_proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:15.557398+00:00
-- url     : https://prove2.me/submissions/ebf215dd-85fc-4f57-8cfa-7a3e55a45044

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DeterminantProjection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.IndefR Formalism.IndefR.DeterminantProjection
variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]
namespace Formalism.IndefR.DeterminantProjection
theorem _root_.solution (u r : n → A) (hru : r ⬝ᵥ u = 1) (x : A) :
    (1 + (x - 1) • (replicateCol Unit u * replicateRow Unit r)).det = x := by
  rw [← Matrix.smul_mul, ← Matrix.replicateCol_smul, det_one_add_replicateCol_mul_replicateRow,
    dotProduct_smul, hru, smul_eq_mul, mul_one]
  ring
end Formalism.IndefR.DeterminantProjection
