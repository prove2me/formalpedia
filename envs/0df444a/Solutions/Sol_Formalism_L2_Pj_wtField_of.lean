-- Prove2me | solution 1 for Formalism.L2.Pj.wtField_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:16:59.106865+00:00
-- url     : https://prove2.me/submissions/cac6c973-9a7a-4e68-a306-3f9383069f06

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameProofs

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
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.L2.Pj
theorem _root_.solution (hD : BorDesc Xo c) : WtField Xo c := by
  intro a n f hf S _ _ t y y' hy hy' hb
  have key : ∀ (p q : TRing c.F) (φ : p.R →ₐ[c.F] S) (ψ : q.R →ₐ[c.F] S) (yp : FrPt Xo c p.R)
      (yq : FrPt Xo c q.R), FrMap φ yp y → FrMap ψ yq y' → ψ (f q yq) = wchar (ex Dw a n) t * φ (f p yp) := by
    intro p q φ ψ yp yq hp hq
    obtain ⟨r, α, β, χ, z, z', t₀, hα, hβ, hz, hz', hb₀, ht⟩ := hD S t y y' hb p q φ ψ yp yq hp hq
    rw [← hα, ← hβ, AlgHom.comp_apply, AlgHom.comp_apply, ← hf.1 p r α yp z hz, ← hf.1 q r β yq z' hz',
      hf.2 r t₀ z z' hb₀, map_mul]
    congr 1
    simp only [wchar, map_prod, map_pow, ht]
  unfold evR evalAt
  rw [dif_pos hy, dif_pos hy']
  exact key _ _ _ _ _ _ hy.choose_spec.choose_spec.choose_spec hy'.choose_spec.choose_spec.choose_spec
end Formalism.L2.Pj
