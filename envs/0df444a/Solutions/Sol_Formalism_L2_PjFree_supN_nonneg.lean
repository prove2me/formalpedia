-- Prove2me | solution 1 for Formalism.L2.PjFree.supN_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:00.114981+00:00
-- url     : https://prove2.me/submissions/ddf6eb95-cddb-4e24-b22e-0b89f211c2b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_JFDFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.L2 Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
namespace Formalism.L2.PjFree
theorem _root_.solution (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : 0 ≤ supN X la P :=
  ENNReal.toReal_nonneg
end Formalism.L2.PjFree
