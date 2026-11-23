-- Prove2me | solution 1 for Formalism.L2.PjFree.supE_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:45.061879+00:00
-- url     : https://prove2.me/submissions/4a2b26e3-4c9a-44fd-83bf-1a3775af6027

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
theorem _root_.solution (a : ℂ) (P : FDSec X) : supE X la (a • P) = ENNReal.ofReal ‖a‖ * supE X la P := by
  unfold supE
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg a)]
  congr 1
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  ring
end Formalism.L2.PjFree
