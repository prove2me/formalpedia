-- Prove2me | solution 1 for Formalism.L2.Pj.nrmC_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:57.621453+00:00
-- url     : https://prove2.me/submissions/1e20f2d0-023a-4c65-a0cf-18487222bf8c

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompData
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Theorems.Thm_Formalism_L2_Pj_nrmC_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {Z : Comp Xo c}
variable (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
  (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
namespace Formalism.L2.Pj
theorem _root_.solution (hfn : FnNe Xo c fn) {G : WTZ E} {f : AC Z} (P : Om Z →+* ℂ) (hf : f ∈ AG Z G) (hf0 : f ≠ 0) :
    0 < nrmC fn yP G f P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  rw [nrmC_single]
  refine mul_pos (norm_pos_iff.2 ((map_ne_zero P).2 hr)) (Finset.prod_pos fun i _ => ?_)
  exact zpow_pos (abs_pos.2 (hfn _ _ i)) _
end Formalism.L2.Pj
