-- Prove2me | solution 1 for Formalism.L2.PjFree.supE_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:44.580941+00:00
-- url     : https://prove2.me/submissions/e701d17c-1611-49e6-87d6-7a91b6321cae

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RulInst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  (X : Comp → Data E r) (la : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r)
namespace Formalism.L2.PjFree
theorem _root_.solution (P Q : FDSec X) : supE X la (P + Q) ≤ supE X la P + supE X la Q := by
  unfold supE
  refine iSup_le fun p => ?_
  have key : (X p.1).pnorm (la p.1) ((P + Q) p.1) p.2 ≤
      (X p.1).pnorm (la p.1) (P p.1) p.2 + (X p.1).pnorm (la p.1) (Q p.1) p.2 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _)
      (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  exact ((ENNReal.ofReal_le_ofReal key).trans ENNReal.ofReal_add_le).trans
    (add_le_add (le_iSup_of_le p le_rfl) (le_iSup_of_le p le_rfl))
end Formalism.L2.PjFree
