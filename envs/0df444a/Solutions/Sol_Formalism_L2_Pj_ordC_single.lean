-- Prove2me | solution 1 for Formalism.L2.Pj.ordC_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:10.823032+00:00
-- url     : https://prove2.me/submissions/a5ac59ba-6bd4-41a3-bfe6-f54818767798

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompData
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd

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
namespace Formalism.L2.Pj
theorem _root_.solution (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) (G : WTZ E) {r : Om Z} (hr : r ≠ 0) :
    ((ordC δ v G (AddMonoidAlgebra.single G r) : ℤ) : WithTop ℤ) = v r + (frW δ G : WithTop ℤ) := by
  have hv : v r ≠ ⊤ := fun h => hr ((AddValuation.top_iff v).1 h)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hv
  simp only [ordC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, ← hn, WithTop.untopD_coe]
  push_cast; rfl
end Formalism.L2.Pj
