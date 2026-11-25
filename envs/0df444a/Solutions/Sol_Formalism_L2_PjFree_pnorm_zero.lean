-- Prove2me | solution 1 for Formalism.L2.PjFree.pnorm_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:16:30.111216+00:00
-- url     : https://prove2.me/submissions/8fdc53fa-bd2e-4f78-a17d-7c1c8ca56bc1

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
theorem _root_.solution (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) : X.pnorm la 0 x = 0 := by
  simp [Data.pnorm]
end Formalism.L2.PjFree
