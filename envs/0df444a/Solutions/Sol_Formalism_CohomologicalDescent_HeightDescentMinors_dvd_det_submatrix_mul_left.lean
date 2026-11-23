-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.dvd_det_submatrix_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:33.833362+00:00
-- url     : https://prove2.me/submissions/c31e2008-dbc6-4c13-8a45-1baa296449dc

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_det_submatrix_mul_eq_sum

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
theorem _root_.solution {α β γ τ : Type} [Fintype β] [Fintype τ] [DecidableEq τ] (x : R)
    (G : Matrix α β R) (P : Matrix β γ R)
    (h : ∀ (f : τ → β) (g : τ → γ), x ∣ (P.submatrix f g).det) (f : τ → α) (g : τ → γ) :
    x ∣ ((G * P).submatrix f g).det := by
  rw [det_submatrix_mul_eq_sum]
  exact Finset.dvd_sum fun r _ => dvd_mul_of_dvd_right (h r g) _
end Formalism.CohomologicalDescent.HeightDescentMinors
