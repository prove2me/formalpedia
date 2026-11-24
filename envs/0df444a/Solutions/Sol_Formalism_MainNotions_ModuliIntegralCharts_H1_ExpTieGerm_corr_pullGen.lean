-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm.corr_pullGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:45:33.817501+00:00
-- url     : https://prove2.me/submissions/c5423f1e-90aa-46eb-8c3e-b90d0802597c

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
private theorem gs_idRes_lemma {X Y : Scheme.{0}} (h : Y ⟶ X) {U : X.Opens} {W : Y.Opens}
    (hV : W ≤ h ⁻¹ᵁ U) (y : Y) (hy : y ∈ W) (x : Γ(X, U)) :
    gs (𝟙 Y) y W ((Y.presheaf.map (homOfLE hV).op).hom ((h.app U).hom x)) = gs h y U x := by
  rw [gs_res (𝟙 Y) y hV hy, gs_pull (𝟙 Y) h y U (hV hy), Category.id_comp]
section Corr
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
end Corr
section Xo
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
end Xo
section Pull
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)
end Pull
section Val
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
end Val
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (H : LB.Gen.Corr L φ ε φ' ε' t t')
    (h : Z ⟶ Y) : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t h) (LB.pullGen L φ' ε' t' h) := by
  intro j j' hj hj' hjj
  have hc : LB.Coh L φ j := fun k1 k2 e => hj k1 k2 (congrArg (fun f => h ≫ f) e)
  have hc' : LB.Coh L φ' j' := fun k1 k2 e => hj' k1 k2 (congrArg (fun f => h ≫ f) e)
  have hx : ∀ k k', φ k = φ' k' → j k = j' k' := fun k k' e => hjj k k' (congrArg (fun f => h ≫ f) e)
  have E := congrArg Units.val (H j j' hc hc' hx)
  apply Units.ext
  simp only [LB.pullGen, res, pullU, Units.coe_map, MonoidHom.coe_coe] at E ⊢
  apply fn_ext
  intro y hy
  have hy1 : h y ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' :=
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k⟩
  erw [gs_res (𝟙 Z) y _ hy, gs_idRes_lemma h _ y hy.1]
  erw [gs_res (𝟙 Z) y _ hy, gs_idRes_lemma h _ y hy.2]
  erw [← gs_res h y inf_le_left hy1, ← gs_res h y inf_le_right hy1]
  exact congrArg _ E
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
