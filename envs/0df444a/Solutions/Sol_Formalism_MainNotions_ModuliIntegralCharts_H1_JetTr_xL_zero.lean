-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.xL_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:15:50.790568+00:00
-- url     : https://prove2.me/submissions/ecfcd349-b369-40c8-a590-da22b7a010c5

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrC
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_spMap_alg_self
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_spMap_algHom_alg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_unit_push
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_ext2
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_jetCoef_aug
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
theorem _root_.solution (hz : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp T.V)) (jetAug : Jet T.V (Fin 1 × Fin d) m →ₐ[T.V] T.V) ≫ xT m = 1)
    (m : ℕ) : spMap ((jetAug : Jet T.Fr (Fin 1 × Fin d) m →ₐ[T.Fr] T.Fr) : Jet T.Fr (Fin 1 × Fin d) m →+* T.Fr) ≫
      xL I xT m = η[I.t'.G].left := by
  apply ext2 I
  · rw [Category.assoc, xL_fst, ← Category.assoc, spMap_comp', jetCoef_aug, ← spMap_comp', Category.assoc,
      unit_push I.m2.cart]
    have e := congrArg CommaMorphism.left (hz m)
    change spMap _ ≫ (xT m).left = (spMap (algebraMap T.V T.V) ≫ 𝟙 _) ≫ η[I.G.G].left at e
    rw [e, spMap_alg_self, Category.id_comp, Category.id_comp]
  · rw [Category.assoc, xL_snd, spMap_algHom_alg, spMap_alg_self, Over.w η[I.t'.G]]
    rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
