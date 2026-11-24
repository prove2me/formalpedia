-- Prove2me | solution 1 for Formalism.Pfun_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:11:12.004685+00:00
-- url     : https://prove2.me/submissions/42ff48e4-538b-4d90-acff-1f9789cb0469

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
namespace Formalism
theorem _root_.solution : Pfun χ 1 = DirichletCharacter.LFunction χ 1 := by simp [Pfun]
end Formalism
