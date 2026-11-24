-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gram_hadamard_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:43.918622+00:00
-- url     : https://prove2.me/submissions/d78df767-61f3-4914-84a8-5ae6581a43e9

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_gramSchmidt_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sqrt_det_gram_eq_prod_norm

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
open InnerProductSpace
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : GramHadamard := by
  intro U _ _ r a
  have h1 : Real.sqrt ‖(Matrix.gram ℂ a).det‖ ≤ ∏ b, ‖a b‖ := by
    rw [sqrt_det_gram_eq_prod_norm]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_gramSchmidt_le a i
  refine ⟨h1, fun R hR => h1.trans ?_⟩
  calc ∏ b, ‖a b‖ ≤ ∏ _b : Fin r, R := Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun b _ => hR b
    _ = R ^ r := by simp
end Formalism.HermitianLatticeCounting.P
