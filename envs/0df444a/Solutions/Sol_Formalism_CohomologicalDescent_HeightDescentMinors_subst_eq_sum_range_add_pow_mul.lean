-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.subst_eq_sum_range_add_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:24.2813+00:00
-- url     : https://prove2.me/submissions/4f759fbd-aa20-4253-b67d-c72d3842efc1

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
theorem _root_.solution {a : R⟦X⟧} (ha : HasSubst a) (K : ℕ) (g : R⟦X⟧) :
    ∃ h : R⟦X⟧, g.subst a = ∑ k ∈ range K, C (coeff k g) * a ^ k + a ^ K * h := by
  induction K generalizing g with
  | zero => exact ⟨g.subst a, by simp⟩
  | succ K ih =>
    obtain ⟨h, hh⟩ := ih (PowerSeries.mk fun p => coeff (p + 1) g)
    refine ⟨h, ?_⟩
    have e : g.subst a = a * (PowerSeries.mk fun p => coeff (p + 1) g).subst a + C (constantCoeff g) := by
      conv_lhs => rw [eq_X_mul_shift_add_const g]
      rw [subst_add ha, subst_mul ha, subst_X ha, subst_C]
      rfl
    rw [e, hh, Finset.sum_range_succ']
    simp only [coeff_mk, coeff_zero_eq_constantCoeff_apply, pow_zero, mul_one]
    have e2 : a * ∑ k ∈ range K, C (coeff (k + 1) g) * a ^ k =
        ∑ k ∈ range K, C (coeff (k + 1) g) * a ^ (k + 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [mul_add, e2]
    ring
end Formalism.CohomologicalDescent.HeightDescentMinors
