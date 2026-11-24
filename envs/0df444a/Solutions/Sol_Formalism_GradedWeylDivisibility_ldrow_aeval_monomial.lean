-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldrow_aeval_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:09.441411+00:00
-- url     : https://prove2.me/submissions/fa0a36c3-49b9-4fb8-9630-1ab6c4f272e6

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_prod_rowDeg
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R)
    (u : Fin k × Fin n →₀ ℕ) (c : R) :
    aeval (fun v : Fin k × Fin n => C (t v.1) * X v) (monomial u c) =
      monomial u (c * ∏ a : Fin k, t a ^ rowDeg u a) := by
  rw [aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul]
  have hC : (u.prod fun v e => (C (t v.1) : MvPolynomial (Fin k × Fin n) R) ^ e) =
      C (∏ a : Fin k, t a ^ rowDeg u a) := by
    rw [← ldrow_prod_rowDeg]
    simp only [Finsupp.prod, map_prod, map_pow]
  rw [hC, algebraMap_eq, map_mul]
  ring
end Formalism.GradedWeylDivisibility
