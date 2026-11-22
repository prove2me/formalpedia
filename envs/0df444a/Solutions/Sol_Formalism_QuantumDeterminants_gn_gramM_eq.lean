-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_gramM_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:32.638402+00:00
-- url     : https://prove2.me/submissions/4de8643c-ad4f-4fc0-b32f-80132ba9d78e

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg

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
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    gramM k r z z' g = (gnB k r z z' g)ᴴ * Hpk k r * gnB k r z z' g := by
  ext i j
  simp only [gramM, herm, gnB, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    _root_.dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring
end Formalism.QuantumDeterminants
