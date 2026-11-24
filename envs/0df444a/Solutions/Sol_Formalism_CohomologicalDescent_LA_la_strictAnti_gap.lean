-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_strictAnti_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:53:12.670475+00:00
-- url     : https://prove2.me/submissions/d62c110f-df72-4990-97f8-075ca9e697bf

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
theorem _root_.solution {r : ℕ} (U : Fin r → ℤ) (hU : StrictAnti U) :
    ∀ (k : ℕ) (a b : Fin r), b.val = a.val + k → U b + k ≤ U a := by
  intro k
  induction k with
  | zero =>
    intro a b h
    have hab : b = a := Fin.ext (by omega)
    subst hab
    simp
  | succ k ih =>
    intro a b h
    have hb := b.isLt
    have hk : a.val + k < r := by omega
    have h1 := ih a ⟨a.val + k, hk⟩ rfl
    have h2 : U b < U ⟨a.val + k, hk⟩ :=
      hU (Fin.lt_iff_val_lt_val.mpr (by show a.val + k < b.val; omega))
    push_cast
    omega
end Formalism.CohomologicalDescent.LA
