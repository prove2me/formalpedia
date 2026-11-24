-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sqrt_det_gram_eq_prod_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:23.18679+00:00
-- url     : https://prove2.me/submissions/a900502f-7d0b-4d82-a346-f537c29ff133

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_gram_eq_prod_gramSchmidt_norm_sq

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
theorem _root_.solution {r : ℕ} (a : Fin r → U) :
    Real.sqrt ‖(Matrix.gram ℂ a).det‖ = ∏ i, ‖gramSchmidt ℂ a i‖ := by
  rw [det_gram_eq_prod_gramSchmidt_norm_sq, norm_prod]
  simp only [norm_pow, Complex.norm_real, norm_norm]
  rw [Finset.prod_pow, Real.sqrt_sq (Finset.prod_nonneg fun _ _ => norm_nonneg _)]
end Formalism.HermitianLatticeCounting.P
