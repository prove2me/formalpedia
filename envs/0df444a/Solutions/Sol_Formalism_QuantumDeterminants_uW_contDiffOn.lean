-- Prove2me | solution 1 for Formalism.QuantumDeterminants.uW_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:10:39.330034+00:00
-- url     : https://prove2.me/submissions/6eff695a-be82-4365-9db0-e9db2b741fa9

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds

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
theorem _root_.solution (l : Fin m) : ContDiffOn ℝ ∞ (uW l) (OmX m) := by
  have h1 : ContDiff ℝ ∞ (fun x : Fin m → ℂ => x l) := contDiff_apply ℝ ℂ l
  have h2 : ContDiff ℝ ∞ (fun x : Fin m → ℂ => ∏ k, Complex.normSq (x k)) := by
    apply contDiff_prod
    intro k _
    have e : (fun x : Fin m → ℂ => Complex.normSq (x k)) = fun x => ‖x k‖ ^ 2 := by
      funext x
      rw [Complex.normSq_eq_norm_sq]
    rw [e]
    exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ k)
  have h3 : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => (∏ k, Complex.normSq (x k))⁻¹) (OmX m) := by
    apply h2.contDiffOn.inv
    intro x hx
    exact Finset.prod_ne_zero_iff.mpr fun k _ => by simpa [Complex.normSq_eq_zero] using hx k
  have h4 := Complex.ofRealCLM.contDiff.comp_contDiffOn h3
  have e : uW l = fun x => x l * (Complex.ofRealCLM ∘ fun x : Fin m → ℂ =>
      (∏ k, Complex.normSq (x k))⁻¹) x := by
    funext x
    simp [uW]
  rw [e]
  exact h1.contDiffOn.mul h4
end Formalism.QuantumDeterminants
