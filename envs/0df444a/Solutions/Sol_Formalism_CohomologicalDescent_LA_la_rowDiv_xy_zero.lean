-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_rowDiv_xy_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:17:17.171079+00:00
-- url     : https://prove2.me/submissions/c3a3edd0-4484-422a-ad69-3407ac187892

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_coeff
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowGen_X
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
theorem _root_.solution (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (a : Fin 2) (p q k : ℕ) :
    rowDiv R a 0 k (la_xy R s p q) =
      (p.choose k : MvPolynomial (Fin 2 × Fin n) R) *
        (X ((0 : Fin 2), s) ^ (p - k) * X (a, s) ^ k * X ((1 : Fin 2), s) ^ q) := by
  have h0 : rowGen R a (0 : Fin 2) (X ((0 : Fin 2), s) : MvPolynomial (Fin 2 × Fin n) R) =
      Polynomial.C (X ((0 : Fin 2), s)) + Polynomial.X * Polynomial.C (X (a, s)) := by
    rw [la_rowGen_X, if_pos rfl]
  have h1 : rowGen R a (0 : Fin 2) (X ((1 : Fin 2), s) : MvPolynomial (Fin 2 × Fin n) R) =
      Polynomial.C (X ((1 : Fin 2), s)) := by
    rw [la_rowGen_X, if_neg (show ¬ ((1 : Fin 2) = 0) by decide), add_zero]
  simp only [rowDiv]
  rw [la_xy, map_mul, map_pow, map_pow, h0, h1, ← Polynomial.C_pow, la_coeff]
end Formalism.CohomologicalDescent.LA
