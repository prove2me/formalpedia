-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.cM_cM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:15:44.883838+00:00
-- url     : https://prove2.me/submissions/92ad7ea0-0e84-446d-b505-22a3fac84a84

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
theorem _root_.solution {m n : Type} (A : Matrix m n ℂ) : cM (cM A) = A := by
  ext i j
  simp [cM]
end Formalism.L2.Pj.FJ
