-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.qM_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:12:31.083244+00:00
-- url     : https://prove2.me/submissions/5cbb9b4c-3850-4517-8dcd-c411628d8457

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K]
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
theorem _root_.solution (p q r s : K) (u v : Fin 4 → K) :
    ∑ β, (∑ a, qM p q r s β a * u a) * (∑ a, qM p q r s β a * v a)
      = (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) * ∑ a, u a * v a := by
  simp [qM, Fin.sum_univ_four]
  ring
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
