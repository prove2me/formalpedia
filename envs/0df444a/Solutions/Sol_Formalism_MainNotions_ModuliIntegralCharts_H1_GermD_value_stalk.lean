-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.value_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:47:59.592276+00:00
-- url     : https://prove2.me/submissions/01079c4d-bbe7-468a-ace0-047f75026573

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
theorem _root_.solution (hL : L.IsLB) (a : ℤ) {T : Over S0} {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (hv : IsValueAt A L a s z τ v) {Z : Scheme.{0}} (r : Z ⟶ T.left) (y : Z) (j : Fin 1 → L.ι)
    (hy : r y ∈ LB.wchart L (fun _ : Fin 1 => z.left) j) :
    gs (r ≫ (ptSecT A z).left) y _ (s.f j) = gs r y ⊤ v * (gm r y _ (τ.s j)).val := by
  have h1 := congrArg (gs r y (LB.wchart L (fun _ : Fin 1 => z.left) j)) (hv j)
  refine ((gs_pull r (ptSecT A z).left y _ (val_le A L z j hy) _).symm.trans
    ((gs_res r y (val_le A L z j) hy _).symm.trans h1)).trans ?_
  exact (gs_mul r y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res r y le_top hy v) (gs_unit r y _ hy _))
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
