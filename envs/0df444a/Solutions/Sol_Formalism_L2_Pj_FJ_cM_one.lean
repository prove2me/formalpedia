-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.cM_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:15:47.567428+00:00
-- url     : https://prove2.me/submissions/3c8e043d-7ebe-409a-b27d-f21f7eda4d4c

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {r ρ : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution : cM (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [cM]
  · simp [cM, Matrix.one_apply, h]
end Formalism.L2.Pj.FJ
