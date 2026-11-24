-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.isValueAt_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:42:48.636473+00:00
-- url     : https://prove2.me/submissions/01b18560-fe99-48f7-af98-51d8d57b812b

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_EvalSinglePointId
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
attribute [local instance] Over.cartesianMonoidalCategory
section Alg
variable {S : Type} [CommRing S] {d : ℕ}
end Alg
section Unit
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
variable {O : Type} [CommRing O] [StarRing O]
end Unit
section Geo
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
private theorem mul_cancel_lemma {R : Type} [CommRing R] (a b c t : R) (h : b * c = 1) :
    a * t = a * b * (c * t) := by
  linear_combination (-(a * t)) * h
end Geo
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
theorem _root_.solution {a : ℤ} {T : Over Xo.X} {s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L a T)}
    {z : T ⟶ Xo.univ.t.G}
    {τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := T.left) (K := Fin 1) (fun _ => z.left) fun _ => a)}
    {v : Γ(T.left, ⊤)} (hv : IsValueAt Xo.univ.t.G Xo.univ.t.PP.L a s z τ v) (w : Γ(T.left, ⊤)ˣ) :
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L a s z (scaleGen _ _ w τ) (v * ((w⁻¹ : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤))) := by
  intro j
  rw [hv j]
  simp only [Formalism.L2.Pj.scaleGen, ReciprocityTheory.ChartRestriction.G.Semi.res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  rw [map_mul]
  exact mul_cancel_lemma _ _ _ _ (by erw [← map_mul, Units.inv_mul, map_one])
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
