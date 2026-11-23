-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.exists_submatrix_det_not_dvd_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:51.078392+00:00
-- url     : https://prove2.me/submissions/da2f3f04-d2f5-46bb-9112-c66a9fb28881

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_det_submatrix_mul_right

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
theorem _root_.solution {ι τ : Type} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]
    (x : R) (h : ℕ) (M M' : Matrix ι ι R) (e : τ → ι) (he : Function.Injective e)
    (hM : M * M' = (x ^ h) • (1 : Matrix ι ι R))
    (hx : ¬ x ^ (Fintype.card τ * h + 1) ∣ x ^ (Fintype.card τ * h)) :
    ∃ f g : τ → ι, ¬ x ^ (Fintype.card τ * h + 1) ∣ (M.submatrix f g).det := by
  by_contra hcon
  push Not at hcon
  apply hx
  have h1 := dvd_det_submatrix_mul_right _ M M' hcon e e
  have h2 : ((x ^ h) • (1 : Matrix ι ι R)).submatrix e e = (x ^ h) • (1 : Matrix τ τ R) := by
    rw [← Matrix.submatrix_one e he]; rfl
  rw [hM, h2, Matrix.det_smul, Matrix.det_one, mul_one, ← pow_mul, mul_comm h] at h1
  exact h1
end Formalism.CohomologicalDescent.HeightDescentMinors
