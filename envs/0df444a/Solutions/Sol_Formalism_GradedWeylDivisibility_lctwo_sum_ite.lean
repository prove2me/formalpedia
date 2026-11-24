-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lctwo_sum_ite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:48.769261+00:00
-- url     : https://prove2.me/submissions/16aa0981-b04c-4348-b450-61bc6593f9a2

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TwoColumn

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
theorem _root_.solution {r : ℕ} (a : Fin r) (e : ℕ) (f : Fin r → ℕ) (P : Fin r → Prop) [DecidablePred P] :
    (∑ b : Fin r with P b, ((if a = b then e else 0) + f b)) =
      (if P a then e else 0) + ∑ b : Fin r with P b, f b := by
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq]
end Formalism.GradedWeylDivisibility
