-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.norm_sum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:24:38.132212+00:00
-- url     : https://prove2.me/submissions/95c1dc92-3471-43ad-b76c-0086eb18475c

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
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → ℚ_[p]) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ s, f i‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (Padic.nonarchimedean _ _).trans (max_le (h a (mem_insert_self _ _)) ?_)
    exact ih (fun i hi => h i (mem_insert_of_mem hi))
end Formalism.GM.gammaIntegralityLemmas
