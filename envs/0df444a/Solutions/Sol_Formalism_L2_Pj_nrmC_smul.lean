-- Prove2me | solution 1 for Formalism.L2.Pj.nrmC_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:51.245675+00:00
-- url     : https://prove2.me/submissions/7ed13e64-8c04-4be1-ae4d-f24425ab1654

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
theorem _root_.solution {G : WTZ E} {f : AC Z} (P : Om Z →+* ℂ) (a : Om Z) (hf : f ∈ AG Z G) :
    nrmC fn yP G (a • f) P = ‖P a‖ * nrmC fn yP G f P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  rw [AddMonoidAlgebra.smul_single', nrmC_single, nrmC_single, map_mul, norm_mul, mul_assoc]
end Formalism.L2.Pj
