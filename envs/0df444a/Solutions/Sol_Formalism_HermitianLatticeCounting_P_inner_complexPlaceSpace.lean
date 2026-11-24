-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.inner_complexPlaceSpace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:48.457801+00:00
-- url     : https://prove2.me/submissions/67a9eb63-9f06-4afd-8306-ba79dbd0b345

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SumComplexEmbeddingsEqSumInfinitePlace

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
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (x y : s5bV E) : inner ℝ x y = ∑ w, (conj (x w) * y w).re := by
  first
  | (simp only [PiLp.inner_apply, Complex.inner]; done)
  | (rw [PiLp.inner_apply]
     refine Finset.sum_congr rfl fun w _ => ?_
     simp only [real_inner_eq_re_inner, RCLike.inner_apply, RCLike.re_to_complex, Complex.mul_re,
       Complex.conj_re, Complex.conj_im]
     ring1)
end Formalism.HermitianLatticeCounting.P
