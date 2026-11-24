-- Prove2me | solution 1 for Formalism.L2.PjFree.pnorm_fac_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:57.223439+00:00
-- url     : https://prove2.me/submissions/302eaa40-7502-4adf-8350-9031e4dd9962

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
theorem _root_.solution (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) :
    0 ≤ ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
end Formalism.L2.PjFree
