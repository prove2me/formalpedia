-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.det_submatrix_mul_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:30.204723+00:00
-- url     : https://prove2.me/submissions/9ba8f5ef-29d8-40f9-b12c-16b14d61a727

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

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
variable {R : Type} [CommRing R]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution {α β γ τ : Type} [Fintype β] [Fintype τ] [DecidableEq τ]
    (G : Matrix α β R) (P : Matrix β γ R) (f : τ → α) (g : τ → γ) :
    ((G * P).submatrix f g).det =
      ∑ r : τ → β, (∏ i, G (f i) (r i)) * (P.submatrix r g).det := by
  classical
  have h : (G * P).submatrix f g = fun i => ∑ k, G (f i) k • (fun j => P k (g j)) := by
    funext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [h]
  have h2 := (Matrix.detRowAlternating : (τ → R) [⋀^τ]→ₗ[R] R).toMultilinearMap.map_sum
    (fun i k => G (f i) k • (fun j => P k (g j)))
  show (Matrix.detRowAlternating : (τ → R) [⋀^τ]→ₗ[R] R).toMultilinearMap _ = _
  rw [h2]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl
end Formalism.CohomologicalDescent.HeightDescentMinors
