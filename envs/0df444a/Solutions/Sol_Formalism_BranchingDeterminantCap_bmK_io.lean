-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_io
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:48:33.62665+00:00
-- url     : https://prove2.me/submissions/eb9893e1-7f58-4499-ac37-b4e1d6da522b

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_IL_of
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_key
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_lin
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_rel_ex
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_rel_add
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_rel_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam sg : Fin n → ℕ)
    (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    ∃ io : ↥(dualWeyl R n n sg) →ₗ[R] BP R n, ∀ (f : ↥(dualWeyl R n n sg)) (G : BP R n),
      bmRel R n lam sg f G → io f = bmZop R n lam sg G := by
  exact bmK_lin (bmRel R n lam sg) (bmZop R n lam sg) (bmK_rel_ex lam sg (bm_IL_of lam sg hI))
    (fun f f' G G' h h' => bmK_rel_add lam sg f f' G G' h h')
    (fun c f G h => bmK_rel_smul lam sg c f G h)
    (fun f G G' h h' => bmK_key lam sg hI (f : MvPolynomial (Fin n × Fin n) R) G G' h h')
end Formalism.BranchingDeterminantCap
