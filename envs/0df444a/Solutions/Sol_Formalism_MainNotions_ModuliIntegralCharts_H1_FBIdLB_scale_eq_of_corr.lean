-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB.scale_eq_of_corr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:50.999803+00:00
-- url     : https://prove2.me/submissions/fb99917f-e008-4801-bdab-23bdd804f2ed

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_res_top_mul
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_le_iSup_piece
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_units_ext_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
theorem _root_.solution (hL : t.PP.L.IsLB) {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ t.G.left)} {ε' : K' → ℤ}
    {g : LB.Gen (LB.LinComb t.PP.L φ ε)} {g' : LB.Gen (LB.LinComb t.PP.L φ' ε')}
    (hc : LB.Gen.Corr t.PP.L φ ε φ' ε' g g') {v v' : Γ(Y, ⊤)ˣ}
    (h : LB.Gen.Corr t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v' g')) : v = v' := by
  refine DVR.units_ext_cover ⊤ (fun ρ => ⊤ ⊓ DVR.piece t.PP.L φ φ' ρ) (fun _ => inf_le_left)
    (DVR.le_iSup_piece t.PP.L φ φ' hL ⊤) v v' fun ρ => ?_
  have hj : LB.Coh t.PP.L φ (ρ ∘ φ) := fun k₁ k₂ e => by simp [e]
  have hj' : LB.Coh t.PP.L φ' (ρ ∘ φ') := fun k₁ k₂ e => by simp [e]
  have hm : ∀ k k', φ k = φ' k' → (ρ ∘ φ) k = (ρ ∘ φ') k' := fun k k' e => by simp [e]
  have e1 := h _ _ hj hj' hm
  have e2 := hc _ _ hj hj' hm
  unfold scaleGenG at e1
  dsimp only at e1
  erw [res_top_mul, res_top_mul, e2, mul_left_inj] at e1
  have e3 := congrArg (res (show ⊤ ⊓ DVR.piece t.PP.L φ φ' ρ ≤
    LB.wchart t.PP.L φ (ρ ∘ φ) ⊓ LB.wchart t.PP.L φ' (ρ ∘ φ') from inf_le_right)) e1
  simpa only [DVR.res_res'] using e3
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
