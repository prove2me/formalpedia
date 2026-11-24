-- Prove2me | solution 1 for Formalism.QuantumDeterminants.uW_hasLineDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:33:38.831611+00:00
-- url     : https://prove2.me/submissions/67e665a7-cdd8-477a-bb34-371a274283a2

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_uW_line

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
variable {m : ℕ}
namespace Formalism.QuantumDeterminants
theorem _root_.solution (l : Fin m) (x : Fin m → ℂ) (hx : x l ≠ 0) (a : ℂ) :
    HasLineDerivAt ℝ (uW l) (-(star a) / (star (x l)) ^ 2 *
      (((∏ k ∈ Finset.univ.erase l, Complex.normSq (x k))⁻¹ : ℝ) : ℂ)) x (Pi.single l a) := by
  set K : ℂ := (((∏ k ∈ Finset.univ.erase l, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) with hK
  have hc : star (x l) ≠ 0 := star_ne_zero.mpr hx
  have h1 : HasDerivAt (fun t : ℝ => star (x l) + (t : ℂ) * star a) (star a) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const (star a)
    simpa using h.const_add (star (x l))
  have h0 : star (x l) + ((0 : ℝ) : ℂ) * star a = star (x l) := by simp
  have hc' : star (x l) + ((0 : ℝ) : ℂ) * star a ≠ 0 := by
    rw [h0]
    exact hc
  have h2 := ((hasDerivAt_inv hc').comp (0 : ℝ) h1).mul_const K
  unfold HasLineDerivAt
  have hf : (fun t : ℝ => uW l (x + t • (Pi.single l a : Fin m → ℂ))) =
      fun t : ℝ => (star (x l) + (t : ℂ) * star a)⁻¹ * K := by
    funext t
    rw [uW_line]
  rw [hf]
  exact h2.congr_deriv (by rw [h0]; ring)
end Formalism.QuantumDeterminants
