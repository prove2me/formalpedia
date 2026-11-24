-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.qM_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:03:19.304459+00:00
-- url     : https://prove2.me/submissions/ce0c5110-16e8-43fd-a690-340598416178

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
theorem _root_.solution (c : K →+* K) {p q r s : K} (hp : c p = p) (hq : c q = q) (hr : c r = r) (hs : c s = s) (β a : Fin 4) :
    c (qM p q r s β a) = qM p q r s β a := by
  fin_cases β <;> fin_cases a <;> simp [qM, hp, hq, hr, hs, map_neg]
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
