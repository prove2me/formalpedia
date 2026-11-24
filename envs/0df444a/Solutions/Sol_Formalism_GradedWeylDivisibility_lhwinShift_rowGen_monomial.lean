-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwinShift_rowGen_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:47.833707+00:00
-- url     : https://prove2.me/submissions/0d3e2153-24ca-436b-b44e-50e358aaa9e6

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwinShift_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwinShift_pow
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwinShift_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwinShift_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwinShift_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    LhwinShift (rowGen R a b (monomial d c)) (Finsupp.weight (lhwinHt r n) d)
      ((a.val : ℤ) - b.val) := by
  unfold rowGen
  rw [aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]
  refine lhwinShift_mul (lhwinShift_algebraMap c _) ?_
  unfold Finsupp.prod Finsupp.sum
  exact lhwinShift_prod _ _ _ _ fun v _ => lhwinShift_pow (lhwinShift_gen a b v) _
end Formalism.GradedWeylDivisibility
