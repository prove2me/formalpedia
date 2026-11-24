-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_rowDiv_tw_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:14:09.112247+00:00
-- url     : https://prove2.me/submissions/76a449ef-3dff-4e06-a651-c68f9d912d6f

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowGen_det_eq
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
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] (a : Fin 2) (k c : ℕ)
    (f : MvPolynomial (Fin 2 × Fin 2) R) :
    rowDiv R a a k (la_det R ^ c * f) = la_det R ^ c *
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, (c.choose x.1 : MvPolynomial (Fin 2 × Fin 2) R) *
        rowDiv R a a x.2 f := by
  simp only [rowDiv]
  rw [map_mul, map_pow, la_rowGen_det_eq, mul_pow, ← Polynomial.C_pow, mul_assoc,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul]
  simp only [Polynomial.coeff_one_add_X_pow]
end Formalism.CohomologicalDescent.LA
