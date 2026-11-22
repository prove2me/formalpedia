-- Prove2me | solution 1 for Comp.mem_stdSimplex_of_isStratQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:38:50.894245+00:00
-- url     : https://prove2.me/submissions/7bdad275-d339-4416-9441-5dab4430adea

import Definitions.Def_Comp_Basic
import Definitions.Def_Comp_MatrixGameQ

set_option autoImplicit true
open Comp
open Csg
variable {I : Type*} [Fintype I]
namespace Comp
theorem _root_.solution {p : I → ℚ} (h : IsStratQ p) :
    (fun i => ((p i : ℚ) : ℝ)) ∈ stdSimplex ℝ I := by
  refine ⟨fun i => ?_, ?_⟩
  · change (0 : ℝ) ≤ ((p i : ℚ) : ℝ)
    exact_mod_cast h.1 i
  · change ∑ i, ((p i : ℚ) : ℝ) = 1
    have hq : ((∑ i, p i : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by rw [h.2]
    push_cast at hq
    exact hq
end Comp
