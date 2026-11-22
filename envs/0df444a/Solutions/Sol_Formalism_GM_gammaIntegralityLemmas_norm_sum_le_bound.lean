-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.norm_sum_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:24:35.895076+00:00
-- url     : https://prove2.me/submissions/658aeaf0-dce9-471f-822c-fb2066c8bb36

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
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → ℚ_[p]) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ i ∈ s, ‖f i‖ ≤ K) : ‖∑ i ∈ s, f i‖ ≤ K := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hK
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (Padic.nonarchimedean _ _).trans (max_le (h a (mem_insert_self _ _)) ?_)
    exact ih (fun i hi => h i (mem_insert_of_mem hi))
end Formalism.GM.gammaIntegralityLemmas
