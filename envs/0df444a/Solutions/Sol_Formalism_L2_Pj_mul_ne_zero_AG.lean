-- Prove2me | solution 1 for Formalism.L2.Pj.mul_ne_zero_AG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:52.223795+00:00
-- url     : https://prove2.me/submissions/f868626f-c19f-4cef-96b3-c163f36d2cd3

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompData

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
namespace Formalism.L2.Pj
theorem _root_.solution {Z : Comp Xo c} {G G' : WTZ E} {f g : AC Z} (hf : f ∈ AG Z G) (hg : g ∈ AG Z G')
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) : f * g ≠ 0 := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  obtain ⟨s, rfl⟩ := mem_AG.1 hg
  have hr : r ≠ 0 := by
    rintro rfl
    exact hf0 (by simp)
  have hs : s ≠ 0 := by
    rintro rfl
    exact hg0 (by simp)
  rw [AddMonoidAlgebra.single_mul_single]
  simp [hr, hs]
end Formalism.L2.Pj
