-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.powOAct_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:04.433794+00:00
-- url     : https://prove2.me/submissions/d5129477-0736-42f8-8d30-27af633d534e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GPowSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GPowPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_powRingAct_pr

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution (hR : BoxRosatiSt) (hT : BoxTauBalSt) : PowOActSt := by
  intro E _ _ _ H V _ _ _ t P n D' pD
  letI := H.starRing
  letI sm : SMul (𝓞 E) D'.toPre.X := ⟨fun a x => pD.xe.symm (a • pD.xe x)⟩
  have hsm : ∀ (a : 𝓞 E) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x :=
    fun a x => pD.xe.apply_symm_apply _
  letI M : Module (𝓞 E) D'.toPre.X :=
    Function.Injective.module (𝓞 E) pD.xe.toAddMonoidHom pD.xe.injective hsm
  refine ⟨M, ?_⟩
  let ρ := powRingAct pD.pw P.oD.onB.toRingAct
  have hpr : ∀ (a : 𝓞 E) (i : Fin n), ρ.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a :=
    fun a i => powRingAct_pr _ _ a i
  have rosati : ∀ a : 𝓞 E, RosatiAdj D'.toPre.P.A D'.toPre.P.L (ρ.act a) (ρ.act (star a)) := fun a =>
    hR V D'.toPre P.D.toPre n pD _ _ _ _ (P.oD.onB.hom a) (P.oD.onB.hom (star a)) (hpr a) (hpr (star a))
      (P.oD.onB.rosati a)
  let oB : D'.toPre.P.OAct (𝓞 E) := { ρ with rosati := rosati }
  refine ⟨{ onB := oB, c_lin := ?_, tau_bal := ?_ }, fun a x i => by rw [hsm]; rfl, fun a i => hpr a i⟩
  · intro a y
    apply pow_ext pD.pw
    intro i
    change D'.toPre.c (a • y) ≫ pD.pw.pr i = (D'.toPre.c y ≫ ρ.act a) ≫ pD.pw.pr i
    rw [pD.c_pr, hsm, Pi.smul_apply, P.oD.c_lin, Category.assoc, hpr, ← Category.assoc, pD.c_pr]
  · intro a
    exact hT V D'.toPre P.D.toPre n pD _ _ _ _ (fun y => a • y) (fun y => star a • y) (P.oD.onB.hom a)
      (P.oD.onB.hom (star a)) (hpr a) (hpr (star a)) (P.oD.onB.rosati a)
      (fun y => P.oD.c_lin a y) (fun y => P.oD.c_lin (star a) y) (P.oD.tau_bal a)
end Formalism.MainNotions.ModuliIntegralCharts.H1
