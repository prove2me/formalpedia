-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf.maps_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:50:06.27527+00:00
-- url     : https://prove2.me/submissions/5020e0d4-d0d6-4141-ba33-b27b7ee95876

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartPrimTrSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartFrameTrA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartPrimTrPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {X Y : Scheme.{0}} {K : Type} [Fintype K]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
theorem _root_.solution {X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (R : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) = pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q)) :
    LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε t) := by
  refine (maps_iff w φ' (fun k => φ' k ≫ F) ε a t (𝟙 Y) (flatGen L F φ' ε t)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).2 ?_
  · refine unit_ext fun y hy => ?_
    have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
    have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
      wchart_pull_le L F φ' j hy
    refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
    refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
    have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (t.s fun k => j k ⟨⟩)
    rw [Category.comp_id] at e
    exact e.symm
  · intro Z r z p q hp hq
    rw [Category.comp_id]
    exact R Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
end Formalism.MainNotions.ModuliIntegralCharts.H1.ChartPrimTrPf
