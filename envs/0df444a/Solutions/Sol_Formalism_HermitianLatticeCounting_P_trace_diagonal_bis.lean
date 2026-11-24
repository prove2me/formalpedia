-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.trace_diagonal_bis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:36.048242+00:00
-- url     : https://prove2.me/submissions/afa77494-8ad8-4186-bb66-42e25e92f3b2

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : TraceDiag := by
  intro X ι _ μ _ _ F h
  have e : ∀ w x, star (F w x) * F w x = ((‖F w x‖^2 : ℝ) : ℂ) := by
    intro w x
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have h1 : ∀ w, (∫ x, ((‖F w x‖^2 : ℝ) : ℂ) ∂μ) = 1 := by
    intro w
    have := h w w
    simp only [e, if_true] at this
    exact this
  have hint : ∀ w, Integrable (fun x => ‖F w x‖^2) μ := by
    intro w
    by_contra hn
    have h2 : ¬ Integrable (fun x => ((‖F w x‖^2 : ℝ) : ℂ)) μ := fun hi => hn (by
      have h4 := hi.re
      simpa [← Complex.ofReal_pow] using h4)
    have h3 := integral_undef h2
    rw [h1 w] at h3
    exact one_ne_zero h3
  rw [integral_finsetSum _ (fun w _ => hint w)]
  have h2 : ∀ w, ∫ x, ‖F w x‖^2 ∂μ = 1 := by
    intro w
    have := h1 w
    rw [integral_complex_ofReal] at this
    exact_mod_cast this
  simp [h2]
end Formalism.HermitianLatticeCounting.P
