-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_rowDiv_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:38.060048+00:00
-- url     : https://prove2.me/submissions/cf45f760-8baf-4ef9-a3ef-d73fba34b145

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
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
theorem _root_.solution (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k N : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k ((N : MvPolynomial (Fin r × Fin n) R) * f) =
      (N : MvPolynomial (Fin r × Fin n) R) * rowDiv R a b k f := by
  simp only [rowDiv, map_mul, map_natCast]
  rw [← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul]
end Formalism.CohomologicalDescent.LA
