-- Prove2me | solution 1 for Bl.general_b_fact_left_more.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:30.960706+00:00
-- url     : https://prove2.me/submissions/6a0a9915-0f01-43b6-a0e4-c4bdbaf8a10b

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftMore_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial IsLocalRing
open Bl Bl.general_b_fact_left_more
variable {n : ℕ}
namespace Bl.general_b_fact_left_more
theorem _root_.solution (p : Fin n → ℂ) (a : MvPolynomial (Fin n) ℂ) :
    a - C (eval p a) ∈ Ideal.span (Set.range fun i => X i - C (p i)) := by
  induction a using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg =>
    have h : f + g - C (eval p (f + g)) = (f - C (eval p f)) + (g - C (eval p g)) := by
      simp only [map_add]; ring
    rw [h]
    exact Ideal.add_mem _ hf hg
  | mul_X f i hf =>
    have h : f * X i - C (eval p (f * X i)) =
        (f - C (eval p f)) * X i + C (eval p f) * (X i - C (p i)) := by
      simp only [map_mul, eval_X]; ring
    rw [h]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ ?_)
    exact Ideal.subset_span ⟨i, rfl⟩
end Bl.general_b_fact_left_more
