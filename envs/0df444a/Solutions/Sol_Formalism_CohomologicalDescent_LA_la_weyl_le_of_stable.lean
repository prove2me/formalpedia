-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_weyl_le_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:51:25.824598+00:00
-- url     : https://prove2.me/submissions/48b31d3e-ad43-42f7-9787-b57e508400dd

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan

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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (L : Submodule R (MvPolynomial (Fin r × Fin n) R)) (h0 : hw R hn ν ∈ L)
    (hs : ∀ (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R), f ∈ L →
      rowDiv R a b k f ∈ L) : weyl R r n hn ν ≤ L := by
  show Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord R w (hw R hn ν)) ≤ L
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact h0
  | cons x w ih => exact hs x.1 x.2.1 x.2.2 _ ih
end Formalism.CohomologicalDescent.LA
