-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.integer_mean_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:03:26.90585+00:00
-- url     : https://prove2.me/submissions/fb4bab1b-6c9f-42ca-ab0d-2afb89e35691

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourFoldOrthogonalSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity
open Finset
namespace Formalism.HermitianLattices.IntegralLatticeDensity
theorem _root_.solution : IntegerMeanLog := by
  intro K _ _ x hx
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx
  have hne : ∀ φ : K →+* ℂ, ‖φ (x : K)‖ ≠ 0 := fun φ => by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero φ).mpr hx'
  rw [← Real.log_prod (fun φ _ => hne φ)]
  apply Real.log_nonneg
  rw [← norm_prod]
  have key : (∏ φ : K →+* ℂ, φ (x : K)) = algebraMap ℚ ℂ (Algebra.norm ℚ (x : K)) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun φ => rfl)
  rw [key, ← Algebra.coe_norm_int x]
  have hN0 : Algebra.norm ℤ x ≠ 0 := by
    intro h0
    have h5 : Algebra.norm ℚ (x : K) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx'
    apply h5
    rw [← Algebra.coe_norm_int x, h0, Int.cast_zero]
  rw [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hN0
end Formalism.HermitianLattices.IntegralLatticeDensity
