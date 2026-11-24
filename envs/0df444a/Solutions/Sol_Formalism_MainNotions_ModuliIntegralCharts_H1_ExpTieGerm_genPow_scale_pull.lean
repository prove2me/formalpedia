-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm.genPow_scale_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:45:35.483678+00:00
-- url     : https://prove2.me/submissions/ae230b18-8c76-4261-85ec-58d6ddce2c7d

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
theorem _root_.solution {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε))
    (h : Z ⟶ Y) (w : Γ(Z, ⊤)ˣ) (k : ℕ) :
    genPow _ _ (scaleGen _ _ w (LB.pullGen Xo.univ.t.PP.L φ ε t h)) k =
      scaleGen _ _ (w ^ k) (LB.pullGen Xo.univ.t.PP.L φ _ (genPow φ ε t k) h) := by
  simp only [genPow, scaleGen, LB.pullGen, mul_pow, map_pow]
  have hp : ∀ {U : Y.Opens} {W : Z.Opens} (hle : W ≤ h ⁻¹ᵁ U) (x : Γ(Y, U)ˣ),
      res hle (pullU h U (x ^ k)) = res hle (pullU h U x) ^ k := fun hle x => by rw [map_pow, map_pow]
  congr 1
  funext j
  congr 1
  exact (hp _ _).symm
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
