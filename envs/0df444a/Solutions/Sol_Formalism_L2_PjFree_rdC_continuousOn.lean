-- Prove2me | solution 1 for Formalism.L2.PjFree.rdC_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:33:22.107801+00:00
-- url     : https://prove2.me/submissions/8addb49b-61c2-41d2-9fd3-839320962775

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
variable {Xo c U}
variable (U)
variable {U} {σ : c.F →+* ℂ}
namespace Formalism.L2.PjFree
theorem _root_.solution (hU : IsUnf (U σ)) {a n} (hd : Dom a n) (f : cusp Xo c U a n) (k : (U σ).Comp) :
    ContinuousOn (rdC U σ a n f k) ((U σ).X k).dom := by
  have hf : (f : Rul Xo c) ∈ sec Xo c a n := by
    have h0 := f.2
    unfold cusp at h0
    exact (Submodule.mem_inf.mp h0).1
  exact (hU.2.2.2.2.1 a n hd f hf k).1.continuousOn
end Formalism.L2.PjFree
