-- Prove2me | solution 1 for Formalism.L2.PjFree.pnorm_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:11:30.362446+00:00
-- url     : https://prove2.me/submissions/d20ccd56-a022-4cc7-aadc-572cda2a5bf6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_JFDFree
import Theorems.Thm_Formalism_L2_PjFree_pnorm_fac_nonneg

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
theorem _root_.solution (X : Data E r) (la : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (P + Q) x ≤ X.pnorm la P x + X.pnorm la Q x := by
  simp only [Data.pnorm, Pi.add_apply]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (pnorm_fac_nonneg X la x)
end Formalism.L2.PjFree
