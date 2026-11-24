-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2.trunc_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:30:43.489445+00:00
-- url     : https://prove2.me/submissions/36c6b95b-c3a5-4c1f-b73f-4a7cde28d8bc

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_MulGenScaleRight
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_corr_scaleGenG
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_pullGen_scaleGenG
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_scaleGenG_scaleGenG
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_unit__homAt_215ffcb691bb
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit__mul_51f5e9f25667


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MvPolynomial (X)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
variable (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
theorem _root_.solution (e : ∀ m, FrTy y d x m) (T U : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ)
    (hstep : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (e (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
      (scaleGen _ _ (unitΓ (U m)) (e m)))
    (hT : ∀ m, Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
      (T (m + 1)) * U m = T m) (m : ℕ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (tw y d x e T (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
      (tw y d x e T m) := by
  have h1 := FBIdLB.pullGen_scaleGenG Xo.univ.t
    (cφ ![jpt y d x (m + 1) (0 : Fin 2), jpt y d x (m + 1) (1 : Fin 2)]) (cε 2) (unitΓ (T (m + 1))) (e (m + 1))
    (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left
  rw [FBIdLB.unitΓ_homAt] at h1
  have key := FBIdLB.corr_scaleGenG Xo.univ.t (hstep m)
    (unitΓ (Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
      (T (m + 1))))
  have hu : unitΓ (Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
      (T (m + 1))) * unitΓ (U m) = unitΓ (T m) := by
    rw [← FBIdSy.unitΓ_mul, hT m]
  have h2 : scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)]) (cε 2)
      (unitΓ (Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
        (T (m + 1)))) (scaleGenG Xo.univ.t _ _ (unitΓ (U m)) (e m)) = tw y d x e T m :=
    (FBIdSy.scaleGenG_scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)]) (cε 2) _ _
      (e m)).trans (congrArg (fun v => scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)])
        (cε 2) v (e m)) hu)
  exact (congrArg₂ (LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _) h1 h2.symm).mpr key
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
