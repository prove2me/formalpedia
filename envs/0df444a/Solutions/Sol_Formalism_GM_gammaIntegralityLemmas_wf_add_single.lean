-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.wf_add_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:25.301043+00:00
-- url     : https://prove2.me/submissions/37d3581c-2e2d-4ad6-b402-224693a5fc67

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (m : σ →₀ ℕ) (i : σ) :
    (wf (p := p) (m + Finsupp.single i 1)) = ((m i + 1 : ℕ) : ℚ_[p]) * wf m := by
  unfold wf
  have h : ∀ x : σ, (((m + Finsupp.single i 1 : σ →₀ ℕ) x).factorial : ℚ_[p]) =
      ((m x).factorial : ℚ_[p]) * (if x = i then ((m i + 1 : ℕ) : ℚ_[p]) else 1) := by
    intro x
    by_cases hx : x = i
    · subst hx; simp [Nat.factorial_succ]; ring
    · simp [hx, Finsupp.single_apply]
  rw [Finset.prod_congr rfl (fun x _ => h x), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp [mul_comm]
end Formalism.GM.gammaIntegralityLemmas
