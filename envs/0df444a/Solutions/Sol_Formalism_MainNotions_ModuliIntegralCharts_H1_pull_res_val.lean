-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.pull_res_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:49:35.007942+00:00
-- url     : https://prove2.me/submissions/56ba7063-f161-4985-a937-9fe990e86898

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullU_res

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V)
    (x : Γ(X, U)ˣ) : res h2 (res h1 x) = res (h2.trans h1) x := by
  apply Units.ext
  change ((X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op).hom (x : Γ(X, U))) = _
  rw [← Functor.map_comp]
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution {X Y : Scheme.{0}} (h : Y ⟶ X) {V : X.Opens} {W : Y.Opens} (hWV : W ≤ h ⁻¹ᵁ V)
    (u : Γ(X, ⊤)ˣ) :
    ((res hWV (pullU h V (res (le_top : V ≤ ⊤) u)) : Γ(Y, W)ˣ) : Γ(Y, W)) =
      (Y.presheaf.map (homOfLE (le_top : W ≤ h ⁻¹ᵁ ⊤)).op).hom ((h.app ⊤).hom (u : Γ(X, ⊤))) := by
  rw [ReciprocityTheory.ChartRestriction.G.DVR.pullU_res, res_res_lemma]
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1
