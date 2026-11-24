-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm.corr_genPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:00:14.126263+00:00
-- url     : https://prove2.me/submissions/7fdf851a-3cad-4853-bc54-6f1998dfedfd

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_key


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
    (Hc : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ' ε' t t') (k : ℕ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (genPow φ ε t k) (genPow φ' ε' t' k) := by
  intro j j' hj hj' hjj
  have key : ∀ {U V : Y.Opens} (hle : V ≤ U) (a : Γ(Y, U)ˣ), res hle (a ^ k) = res hle a ^ k :=
    fun hle a => map_pow _ a k
  show res _ (t.s j ^ k) = res _ (t'.s j' ^ k)
  erw [key, key]
  exact congrArg (· ^ k) (Hc j j' hj hj' hjj)
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
