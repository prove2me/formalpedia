-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.primUniqOfGlobal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:34:59.790431+00:00
-- url     : https://prove2.me/submissions/ced8bfd6-b745-40dd-bbef-7bfed3f45e5a

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_wchart_cover
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_gen_ratio
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_unit_sec
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_pull_unit_eq_one

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution : PrimUniqOfGlobalSt := by
  intro hglob E _ _ _ H Dw l Xo hab wP wP' hP hP'
  obtain ⟨u, hu⟩ := gen_ratio _ (wchart_cover Xo.univ.t.PP.L Xo.univ.t.PP.isLB _) wP wP' hP.1 hP'.1
  have h1 := pull_unit_eq_one Xo.univ.t.PP.L Xo.univ.t.PP.isLB _ _ (eSec Xo.univ.t.G) (eSec Xo.univ.t.G)
    Xo.univ.t.PP.rig wP wP' u hu hP.2 hP'.2
  have hu1 : u = 1 := by
    obtain ⟨ι, hι⟩ := unit_sec (S := Xo.X)
    obtain ⟨c, hc⟩ := (hglob _ _ hab).2 (u : Γ(Xo.univ.t.G.left, ⊤))
    have e1 : eSec Xo.univ.t.G ≫ Xo.univ.t.G.hom = (𝟙_ (Over Xo.X)).hom := Over.w _
    have hc1 : c = 1 := by
      calc c = (ι ≫ (𝟙_ (Over Xo.X)).hom).appTop.hom c := by rw [hι]; simp
        _ = ι.appTop.hom ((eSec Xo.univ.t.G).appTop.hom (Xo.univ.t.G.hom.appTop.hom c)) := by
            rw [← e1, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]; rfl
        _ = 1 := by
            rw [hc]
            change ι.appTop.hom (((eSec Xo.univ.t.G).app ⊤).hom (u : Γ(Xo.univ.t.G.left, ⊤))) = 1
            rw [h1]
            exact map_one _
    apply Units.ext
    rw [← hc, hc1, map_one, Units.val_one]
  subst hu1
  cases wP
  cases wP'
  congr
  funext j
  simpa using hu j
end Formalism.MainNotions.ModuliIntegralCharts.H1
