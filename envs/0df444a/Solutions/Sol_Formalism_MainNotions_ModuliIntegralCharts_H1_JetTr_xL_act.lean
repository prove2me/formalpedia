-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.xL_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:52:57.313914+00:00
-- url     : https://prove2.me/submissions/ab7f2b71-d191-4fd3-9706-a07d44833c35

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrC
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_spMap_algHom_alg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_jetCoef_substP
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_ext2
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_xL_fst


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
theorem _root_.solution (actT : Fin d → MvPowerSeries (Fin 1 × Fin d) T.V) (a : 𝓞 E) (m : ℕ) (ha : xT m ≫ I.G.act.act a =
      Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (actT p.2)) ≫ xT m) :
    xL I xT m ≫ (I.t'.act.act a).left =
      spMap ((jetSubstP m fun p : Fin 1 × Fin d => MvPolynomial.map (algebraMap T.V T.Fr) (psTrunc m (actT p.2)) :
        Jet T.Fr (Fin 1 × Fin d) m →ₐ[T.Fr] Jet T.Fr (Fin 1 × Fin d) m) :
          Jet T.Fr (Fin 1 × Fin d) m →+* Jet T.Fr (Fin 1 × Fin d) m) ≫ xL I xT m := by
  apply ext2 I
  · rw [Category.assoc, I.m2.act a, ← Category.assoc, xL_fst, Category.assoc, Category.assoc, xL_fst,
      ← Category.assoc (spMap _) (spMap _), spMap_comp', ← jetCoef_substP, ← spMap_comp', Category.assoc]
    exact congrArg (spMap (jc (d := d) 1 m) ≫ ·) (congrArg CommaMorphism.left ha)
  · rw [Category.assoc, Over.w (I.t'.act.act a), Category.assoc, xL_snd, spMap_algHom_alg]
end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
