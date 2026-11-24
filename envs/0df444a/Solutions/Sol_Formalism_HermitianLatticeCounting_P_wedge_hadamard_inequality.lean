-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.wedge_hadamard_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:20.379238+00:00
-- url     : https://prove2.me/submissions/156516b3-1732-4ed2-aeec-5a0518bc5737

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_gramSchmidt_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_det_sesquilinear_le_gramSchmidt

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
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : WedgeHadamard := by
  intro V₁ V₂ _ _ _ _ B hB j y y'
  have := norm_det_sesquilinear_le_gramSchmidt B 1 zero_le_one (fun x y => by rw [one_mul]; exact hB x y) y y'
  rw [one_pow, one_mul] at this
  refine this.trans ?_
  apply mul_le_mul
  · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_gramSchmidt_le y i
  · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_gramSchmidt_le y' i
  · exact Finset.prod_nonneg fun _ _ => norm_nonneg _
  · exact Finset.prod_nonneg fun _ _ => norm_nonneg _
end Formalism.HermitianLatticeCounting.P
