-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2.pe_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:30:40.729229+00:00
-- url     : https://prove2.me/submissions/1f13b260-05b5-434d-a4a7-be5c99e1a93e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_MulGenScaleRight
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_pullGen_scaleGenG
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_unit__homAt_215ffcb691bb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_sub


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
theorem _root_.solution (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (m : ℕ) {n' : ℕ}
    (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S) :
    pe y d x (tw y d x e T) m φ = scaleGenG Xo.univ.t _ _ (unitΓ (sub d m φ (T m))) (pe y d x e m φ) := by
  have h1 := FBIdLB.pullGen_scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)]) (cε 2)
    (unitΓ (T m)) (e m) (homAt y.x (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left
  rw [FBIdLB.unitΓ_homAt] at h1
  exact h1
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
