-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.xL_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:43:08.273996+00:00
-- url     : https://prove2.me/submissions/fbf073f1-268c-4543-a787-853cc11b7d7e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrC
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_spMap_algHom_alg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_ext2
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_jetCoef_trunc
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
theorem _root_.solution (ht : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
      (jetTrunc : Jet T.V (Fin 1 × Fin d) (m + 1) →ₐ[T.V] Jet T.V (Fin 1 × Fin d) m) ≫ xT (m + 1) = xT m)
    (m : ℕ) : spMap ((jetTrunc : Jet T.Fr (Fin 1 × Fin d) (m + 1) →ₐ[T.Fr] Jet T.Fr (Fin 1 × Fin d) m) :
      Jet T.Fr (Fin 1 × Fin d) (m + 1) →+* Jet T.Fr (Fin 1 × Fin d) m) ≫ xL I xT (m + 1) = xL I xT m := by
  apply ext2 I
  · rw [Category.assoc, xL_fst, xL_fst, ← Category.assoc, spMap_comp', jetCoef_trunc, ← spMap_comp',
      Category.assoc]
    exact congrArg (spMap (jc (d := d) 1 m) ≫ ·) (congrArg CommaMorphism.left (ht m))
  · rw [Category.assoc, xL_snd, xL_snd, spMap_algHom_alg]
end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
