-- Prove2me | solution 1 for Formalism.measurable_Gchi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:46:29.118699+00:00
-- url     : https://prove2.me/submissions/ac1e5799-d4bf-4160-a38b-723eb49e017a

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
import Theorems.Thm_Formalism_Schi_eq_Sa
import Theorems.Thm_Formalism_twist_bound

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
open ArithmeticFunction
namespace Formalism
theorem _root_.solution (h3 : MellinSgen) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Measurable (Gchi χ) := by
  have := (h3 _ 1 (twist_bound χ)).1
  unfold Gchi
  rw [Schi_eq_Sa]
  fun_prop
end Formalism
