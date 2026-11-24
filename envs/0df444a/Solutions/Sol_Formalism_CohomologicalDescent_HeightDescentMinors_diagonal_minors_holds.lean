-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.diagonal_minors_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:39:37.156847+00:00
-- url     : https://prove2.me/submissions/62db98eb-0924-478f-87b3-225d91c86f12

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_minors_dvd_mul_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : DiagMinors := by
  intro R _ n t S x a G H hS
  refine minors_dvd_mul_holds R n n n n t (x ^ S) G _ H ?_
  intro f g hf hg
  have h1 : (Matrix.diagonal (fun j => x ^ a j)).submatrix f g =
      Matrix.of fun i j => (x ^ a (f i)) * ((1 : Matrix (Fin n) (Fin n) R).submatrix f g) i j := by
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  rw [h1, Matrix.det_mul_column (fun i => x ^ a (f i)), Finset.prod_pow_eq_pow_sum]
  refine Dvd.dvd.mul_right (pow_dvd_pow x ?_) _
  have h2 := hS (Finset.univ.image f) (by rw [Finset.card_image_of_injective _ hf.injective]; simp)
  rwa [Finset.sum_image (fun i _ j _ h => hf.injective h)] at h2
end Formalism.CohomologicalDescent.HeightDescentMinors
