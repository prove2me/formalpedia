-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.wf_add_single_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:25.300658+00:00
-- url     : https://prove2.me/submissions/6bf3c6fa-44a2-4810-a4a5-b58b0e9ea1d3

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (δ : σ →₀ ℕ) (y : σ) (t : ℕ) :
    wf (p := p) (δ + Finsupp.single y t) * ((δ y).factorial : ℚ_[p]) = wf δ * ((δ y + t).factorial : ℚ_[p]) := by
  unfold wf
  rw [← Finset.mul_prod_erase univ _ (mem_univ y), ← Finset.mul_prod_erase univ (fun x => ((δ x).factorial : ℚ_[p])) (mem_univ y)]
  have : ∀ v ∈ univ.erase y, (((δ + Finsupp.single y t : σ →₀ ℕ) v).factorial : ℚ_[p]) = ((δ v).factorial : ℚ_[p]) := by
    intro v hv
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (ne_of_mem_erase hv)), add_zero]
  rw [Finset.prod_congr rfl this]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  ring
end Formalism.GM.gammaIntegralityLemmas
