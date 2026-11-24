-- Prove2me | solution 1 for Formalism.IndefR.DeterminantProjection.proj_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:15.589039+00:00
-- url     : https://prove2.me/submissions/15ea7377-e353-4b47-81ec-2fe37ba158c2

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
theorem _root_.solution (u r : n → A) (hru : r ⬝ᵥ u = 1) :
    (replicateCol Unit u * replicateRow Unit r) * (replicateCol Unit u * replicateRow Unit r) =
      replicateCol Unit u * replicateRow Unit r := by
  ext i j
  simp only [Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Finset.univ_unique,
    Finset.sum_singleton]
  rw [show (∑ k, u i * r k * (u k * r j)) = u i * (∑ k, r k * u k) * r j by
    rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring]
  rw [show (∑ k, r k * u k) = r ⬝ᵥ u from rfl, hru, mul_one]
end Formalism.IndefR.DeterminantProjection
