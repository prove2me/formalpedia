-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.resolution_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:19.462191+00:00
-- url     : https://prove2.me/submissions/d01705c5-89fa-4a6d-bd0e-06c2ab4b5c7a

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
theorem _root_.solution {Ω T : Type} [MeasurableSpace Ω] (μ : Measure Ω) [NormedAddCommGroup T]
    [InnerProductSpace ℂ T] (v : Ω → T)
    (hres : ∀ x y : T, (∫ k, inner ℂ x (v k) * inner ℂ (v k) y ∂μ) = inner ℂ x y) (x : T) :
    Integrable (fun k => ‖inner ℂ x (v k)‖ ^ 2) μ ∧ (∫ k, ‖inner ℂ x (v k)‖ ^ 2 ∂μ) = ‖x‖ ^ 2 := by
  have e : ∀ k, inner ℂ x (v k) * inner ℂ (v k) x = ((‖inner ℂ x (v k)‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [← inner_conj_symm (v k) x, Complex.mul_conj']; push_cast; rfl
  have h1 : (∫ k, ((‖inner ℂ x (v k)‖ ^ 2 : ℝ) : ℂ) ∂μ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    have := hres x x
    simp only [e] at this
    rw [this, inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hint : Integrable (fun k => ‖inner ℂ x (v k)‖ ^ 2) μ := by
    by_cases hx : x = 0
    · subst hx; simp
    by_contra hn
    have h2 : ¬ Integrable (fun k => ((‖inner ℂ x (v k)‖ ^ 2 : ℝ) : ℂ)) μ := fun hi => hn (by
      have h4 := hi.re
      simpa [← Complex.ofReal_pow] using h4)
    have h3 := integral_undef h2
    rw [h1] at h3
    have : ‖x‖ ^ 2 = 0 := by exact_mod_cast h3
    exact hx (by simpa using this)
  refine ⟨hint, ?_⟩
  rw [integral_complex_ofReal] at h1
  exact_mod_cast h1
end Formalism.HermitianLatticeCounting.P
