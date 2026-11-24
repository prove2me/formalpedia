-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.orbDom_of_latZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:53:04.2568+00:00
-- url     : https://prove2.me/submissions/a30031f6-fc26-4ace-90d4-cc704ad68389

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Theorems.Thm_Formalism_L2_Pj_FJ_zBas_skew
import Theorems.Thm_Formalism_L2_Pj_FJ_zAct_mem_dom

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution {Comp : Type} (X : Comp → Data E r) (h : LatZ X ρ) : OrbDom X ρ := by
  intro cu t x hx
  exact zAct_mem_dom (X cu.1) cu.2 (fun k => zBas_skew _ _ (h cu) k) t x hx
end Formalism.L2.Pj.FJ
