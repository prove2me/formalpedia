-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.inner_placeEmbedding_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:27.45257+00:00
-- url     : https://prove2.me/submissions/d5ebd3c2-45c6-4501-b11d-2d6b7b69fe61

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SumComplexEmbeddingsEqSumInfinitePlace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_trace_eq_sum_infinitePlace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5bSig_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_inner_complexPlaceSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open NumberField
open NumberField
open NumberField
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hc : ∀ w : InfinitePlace E, w.IsComplex) (a z : E) :
    inner ℝ (complexEmbeddingVector a) (WithLp.toLp 2 (fun w : InfinitePlace E => 2 * conj (w.embedding z)) : s5bV E) =
      ((Algebra.trace ℚ E (z * a) : ℚ) : ℝ) := by
  rw [inner_complexPlaceSpace, trace_eq_sum_infinitePlace hc]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [s5bSig_apply, Complex.mul_re, Complex.mul_im]
  ring
end Formalism.HermitianLatticeCounting.P
