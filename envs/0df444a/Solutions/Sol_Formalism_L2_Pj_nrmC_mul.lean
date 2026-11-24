-- Prove2me | solution 1 for Formalism.L2.Pj.nrmC_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:49.260883+00:00
-- url     : https://prove2.me/submissions/4be6112b-267a-4edd-8e98-46ed6435b374

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompData
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Theorems.Thm_Formalism_L2_Pj_exZ_add
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
theorem _root_.solution (hfn : FnNe Xo c fn) {G G' : WTZ E} {f g : AC Z} (P : Om Z →+* ℂ) (hf : f ∈ AG Z G)
    (hg : g ∈ AG Z G') : nrmC fn yP (G + G') (f * g) P = nrmC fn yP G f P * nrmC fn yP G' g P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  obtain ⟨s, rfl⟩ := mem_AG.1 hg
  rw [AddMonoidAlgebra.single_mul_single, nrmC_single, nrmC_single, nrmC_single, map_mul, norm_mul]
  have : ∏ i, |fn _ (yP P) i| ^ (-exZ Dw (G + G') i) =
      (∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i)) * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G' i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [exZ_add, neg_add, zpow_add₀ (abs_ne_zero.2 (hfn _ _ i))]
  rw [this]; ring
end Formalism.L2.Pj
