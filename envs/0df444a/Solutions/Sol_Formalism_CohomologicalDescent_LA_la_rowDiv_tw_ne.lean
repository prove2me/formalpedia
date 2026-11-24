-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_rowDiv_tw_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:14:55.356807+00:00
-- url     : https://prove2.me/submissions/2cc33030-a8f0-4f1c-8f00-6524a3b9b984

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowGen_det_ne
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
theorem _root_.solution (R : Type) [CommRing R] (a b : Fin 2) (hab : a ≠ b) (k c : ℕ)
    (f : MvPolynomial (Fin 2 × Fin 2) R) :
    rowDiv R a b k (la_det R ^ c * f) = la_det R ^ c * rowDiv R a b k f := by
  simp only [rowDiv]
  rw [map_mul, map_pow, la_rowGen_det_ne R a b hab, ← Polynomial.C_pow, Polynomial.coeff_C_mul]
end Formalism.CohomologicalDescent.LA
