-- Prove2me | solution 1 for Formalism.L2.Pj.ordC_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:25:00.712856+00:00
-- url     : https://prove2.me/submissions/848077ee-c6cf-447f-a257-b717c3aeb2bb

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompData
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Theorems.Thm_Formalism_L2_Pj_frW_add
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
theorem _root_.solution (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) {G G' : WTZ E} {f g : AC Z}
    (hf : f ∈ AG Z G) (hg : g ∈ AG Z G') (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    ordC δ v (G + G') (f * g) = ordC δ v G f + ordC δ v G' g := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  obtain ⟨s, rfl⟩ := mem_AG.1 hg
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  have hs : s ≠ 0 := fun h => hg0 (by simp [h])
  rw [AddMonoidAlgebra.single_mul_single]
  apply WithTop.coe_injective
  rw [ordC_single δ v _ (mul_ne_zero hr hs)]
  push_cast
  rw [ordC_single δ v _ hr, ordC_single δ v _ hs, AddValuation.map_mul, frW_add]
  push_cast
  ac_rfl
end Formalism.L2.Pj
