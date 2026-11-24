-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_A_closed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:49.862689+00:00
-- url     : https://prove2.me/submissions/e16b2dc5-4f73-45e6-b541-0ff7ff7f4ccc

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (R : ℝ) (d r : ℕ) (t : ℝ) : IsClosed (s5b7_A R d r t) := by
  have h1 : IsClosed {a : Fin r → EuclideanSpace ℂ (Fin d) | ∀ b, ‖a b‖ ≤ R} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun b => isClosed_le (by fun_prop) continuous_const
  have h2 : Continuous fun a : Fin r → EuclideanSpace ℂ (Fin d) =>
      Real.sqrt ‖(Matrix.gram ℂ a).det‖ := by
    refine Real.continuous_sqrt.comp (continuous_norm.comp (Continuous.matrix_det ?_))
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.gram_apply]
    exact (continuous_apply i).inner (continuous_apply j)
  exact h1.inter (isClosed_le h2 continuous_const)
end Formalism.HermitianLatticeCounting.P
