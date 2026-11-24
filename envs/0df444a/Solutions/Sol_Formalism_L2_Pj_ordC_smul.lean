-- Prove2me | solution 1 for Formalism.L2.Pj.ordC_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:16:30.670842+00:00
-- url     : https://prove2.me/submissions/43be1895-087d-4f81-a9b8-72101e03eaf6

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompData
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Theorems.Thm_Formalism_L2_Pj_ordC_single

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
theorem _root_.solution (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) {G : WTZ E} {f : AC Z} (a : Om Z)
    (hf : f ∈ AG Z G) (hf0 : f ≠ 0) (ha : a ≠ 0) :
    ((ordC δ v G (a • f) : ℤ) : WithTop ℤ) = v a + (ordC δ v G f : WithTop ℤ) := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  rw [AddMonoidAlgebra.smul_single', ordC_single δ v _ (mul_ne_zero ha hr), ordC_single δ v _ hr,
    AddValuation.map_mul, add_assoc]
end Formalism.L2.Pj
