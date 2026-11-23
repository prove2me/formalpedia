-- Prove2me | solution 1 for Formalism.CountingSumsFrames.gram_weylDim_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:43.045404+00:00
-- url     : https://prove2.me/submissions/9167507d-f035-4c14-840c-78f5e0300f0b

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrameMultinomialBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Real
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (n : ℕ) (A : ℤ) (μ : Fin n → ℤ) :
    weylDim (n + 1) (Fin.cons A μ : Fin (n + 1) → ℤ) =
      (∏ j : Fin n, ((((A - μ j : ℤ)) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) * weylDim n μ := by
  unfold weylDim
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, lt_self_iff_false, if_false, one_mul, Fin.succ_pos, if_true,
      Fin.val_succ, Fin.val_zero]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    push_cast
    ring
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_succ, Fin.cons_zero, Fin.not_lt_zero, if_false, one_mul, Fin.succ_lt_succ_iff,
      Fin.val_succ]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    split_ifs
    · push_cast
      congr 1 <;> ring
    · rfl
end Formalism.CountingSumsFrames
