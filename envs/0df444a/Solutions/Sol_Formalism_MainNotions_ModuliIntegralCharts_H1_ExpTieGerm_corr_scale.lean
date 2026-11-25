-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm.corr_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:23:23.07784+00:00
-- url     : https://prove2.me/submissions/164777a4-d4ce-4107-a7a5-849414714198

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_res_res__736ae4318705
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_key
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
theorem _root_.solution {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ Xo.univ.t.G.left)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)} {t' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ' ε')}
    (Hc : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ' ε' t t') (w : Γ(Y, ⊤)ˣ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (scaleGen φ ε w t) (scaleGen φ' ε' w t') := by
  intro j j' hj hj' hjj
  have e := Hc j j' hj hj' hjj
  have key : ∀ {U V : Y.Opens} (hle : V ≤ U) (a b : Γ(Y, U)ˣ), res hle (a * b) = res hle a * res hle b :=
    fun hle a b => map_mul _ a b
  erw [key, key, res_res', res_res', e]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
