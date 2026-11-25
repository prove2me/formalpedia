-- Prove2me | solution 1 for Formalism.L2.PjFree.IsNormOn.of_goodOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:11:04.487251+00:00
-- url     : https://prove2.me/submissions/3b04d8b3-a1ef-4403-bd15-83f369d3682b

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RulInst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Theorems.Thm_Formalism_L2_PjFree_norm_goodOf

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
namespace Formalism.L2.PjFree
namespace IsNormOn
theorem _root_.solution {C : Submodule c.F (Rul Xo c)} {σ : c.F →+* ℂ} {N : Rul Xo c → ℝ}
    (h : IsNormOn C (goodOf c σ) N) : IsNormOn C σ N := by
  exact ⟨h.nonneg, h.defin, fun a f hf => by rw [h.smul a f hf, norm_goodOf], h.add⟩
end IsNormOn
end Formalism.L2.PjFree
