-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.expUniqRaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:27:17.53231+00:00
-- url     : https://prove2.me/submissions/7d58bb7d-b681-42dd-82df-fb6690579c9f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqGlue
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_bcO_left
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_isExpHomR_bc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_sameTan_bc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_theta
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqBC_expUniqLoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_JGPf_jetGlue


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
theorem _root_.solution : ExpUniqRawSt := by
  intro E _ _ _ H Dw l Xo S _ _ x0 d x x' hx hx' ht
  funext m
  apply Over.OverMorphism.ext
  refine ReciprocityTheory.ChartRestriction.G.TB.JGPf.jetGlue S (Fin 1 × Fin d) m Xo.univ.t.G.left (x m).left (x' m).left ?_
  intro p _
  obtain ⟨θ, hθ⟩ := theta p (Fin 1 × Fin d) m
  have hloc := ExpUniqBC.expUniqLoc E H Dw l Xo (Localization.AtPrime p)
    (x0T (algebraMap S (Localization.AtPrime p)) x0) d _ _ (isExpHomR_bc (algebraMap S (Localization.AtPrime p)) x0 hx)
    (isExpHomR_bc (algebraMap S (Localization.AtPrime p)) x0 hx') (sameTan_bc (algebraMap S (Localization.AtPrime p)) x0 ht)
  have hm := congrArg (fun g => (g m).left) hloc
  simp only [xT, Over.comp_left, bcO_left] at hm
  have key : Spec.map (CommRingCat.ofHom (algebraMap (ReciprocityTheory.ChartRestriction.G.TB.JetRing S (Fin 1 × Fin d) m)
      (ReciprocityTheory.ChartRestriction.G.TB.JetLoc S (Fin 1 × Fin d) m p))) =
      Spec.map (CommRingCat.ofHom θ) ≫
        Spec.map (CommRingCat.ofHom (bcJ (algebraMap S (Localization.AtPrime p)) (Fin 1 × Fin d) m)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) hθ.symm
  have e1 := (congrArg (fun t => t ≫ (x m).left) key).trans (Category.assoc _ _ _)
  have e2 := (congrArg (fun t => t ≫ (x' m).left) key).trans (Category.assoc _ _ _)
  exact e1.trans ((congrArg (fun t => Spec.map (CommRingCat.ofHom θ) ≫ t) hm).trans e2.symm)
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
