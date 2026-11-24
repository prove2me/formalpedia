-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.betaUniq_of_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:58:34.31953+00:00
-- url     : https://prove2.me/submissions/6df2f400-ef35-4579-b357-2070c19feebc

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeBeta
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeBeta_pull_unit_eq_one_k
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_gen_ratio
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_isAbelianScheme_univ
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_wchart_cover


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
theorem _root_.solution (hglob : GlobalFnsSt) : BetaUniqSt := by
  intro E _ _ _ H Dw l Xo a β β' hβ hβ' hc hc'
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  obtain ⟨u, hu⟩ := gen_ratio _ (wchart_cover Xo.univ.t.PP.L hL _) β β' hβ hβ'
  have h1 := GaugeBeta.pull_unit_eq_one_k Xo.univ.t.PP.L hL _ _ (eSec Xo.univ.t.G)
    (eSec Xo.univ.t.G) (-3) (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) β β' u hu hc hc'
  have hu1 : u = 1 := by
    obtain ⟨v, hv⟩ := (hglob _ Xo.univ.t.G (isAbelianScheme_univ Xo)).2 (u : Γ(Xo.univ.t.G.left, ⊤))
    have hw : eSec Xo.univ.t.G ≫ Xo.univ.t.G.hom = 𝟙 _ := by
      unfold eSec
      exact Over.w _
    have e1 : (Scheme.Hom.app (eSec Xo.univ.t.G) ⊤).hom
        ((Scheme.Hom.appTop Xo.univ.t.G.hom).hom v) = v := by
      have := congrArg (fun f => (Scheme.Hom.appTop f).hom v) hw
      simp at this
      exact this
    rw [hv] at e1
    have hv1 : v = 1 := e1.symm.trans h1
    apply Units.ext
    rw [← hv, hv1, map_one]
    rfl
  cases β
  cases β'
  congr 1
  funext j
  have hj := hu j
  rw [hu1, map_one, one_mul] at hj
  exact hj
end Formalism.MainNotions.ModuliIntegralCharts.H1
