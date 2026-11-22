-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.dvd_det_submatrix_of_minorsDvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:01.408583+00:00
-- url     : https://prove2.me/submissions/c50d78d0-138c-4215-be72-8b17fdad213b

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
theorem _root_.solution {m p t : ℕ} (x : R) (P : Matrix (Fin m) (Fin p) R) (h : MinorsDvd x t P)
    (f : Fin t → Fin m) (g : Fin t → Fin p) : x ∣ (P.submatrix f g).det := by
  by_cases hf : Function.Injective f
  swap
  · simp only [Function.Injective, not_forall] at hf
    obtain ⟨i, j, hij, hne⟩ := hf
    rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [Matrix.submatrix_apply, hij])]
    exact dvd_zero _
  by_cases hg : Function.Injective g
  swap
  · simp only [Function.Injective, not_forall] at hg
    obtain ⟨i, j, hij, hne⟩ := hg
    rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix_apply, hij])]
    exact dvd_zero _
  have hf' : StrictMono (f ∘ Tuple.sort f) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
  have hg' : StrictMono (g ∘ Tuple.sort g) :=
    (Tuple.monotone_sort g).strictMono_of_injective (hg.comp (Tuple.sort g).injective)
  have h1 := h _ _ hf' hg'
  have h2 : P.submatrix (f ∘ Tuple.sort f) (g ∘ Tuple.sort g) =
      ((P.submatrix f g).submatrix (Tuple.sort f) id).submatrix id (Tuple.sort g) := by
    ext i j; rfl
  rw [h2, Matrix.det_permute', Matrix.det_permute] at h1
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Tuple.sort f)) with e1 | e1 <;>
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Tuple.sort g)) with e2 | e2 <;>
  simpa [e1, e2] using h1
end Formalism.CohomologicalDescent.HeightDescentMinors
