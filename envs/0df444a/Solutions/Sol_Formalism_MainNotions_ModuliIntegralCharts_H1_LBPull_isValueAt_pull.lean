-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isValueAt_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:55.925797+00:00
-- url     : https://prove2.me/submissions/8ad44243-8a8e-4355-b3dc-bd788ac7057b

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LBPull
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_LBPull_ptSecT_whisker

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
theorem _root_.solution {T T' : Over S0} (g : T' ⟶ T) (z : T ⟶ A) {s : LB.Sec (LPow A L a T)}
    {s' : LB.Sec (LPow A L a T')} (hs : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) s s')
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (hv : IsValueAt A L a s z τ v) :
    IsValueAt A L a s' (g ≫ z) (LB.pullGen L (fun _ => z.left) (fun _ => a) τ g.left) (g.left.appTop.hom v) := by
  intro j
  have hW : ∀ x ∈ LB.wchart L (fun _ : Fin 1 => (g ≫ z).left) j,
      g.left x ∈ LB.wchart L (fun _ : Fin 1 => z.left) j := fun x hx =>
    Set.mem_iInter.2 fun k => by
      have h1 := Set.mem_iInter.1 hx k
      simpa [Over.comp_left, Scheme.Hom.comp_base] using h1
  apply fn_ext
  intro x hx
  have hx' := hW x hx
  have hPz := val_le A L z j hx'
  have hPgz := val_le A L (g ≫ z) j hx

  erw [gs_res _ x _ hx, gs_pull (𝟙 _) _ x _ hPgz, Category.id_comp, hs j,
    gs_res _ x _ hPgz, gs_pull (ptSecT A (g ≫ z)).left (g ▷ A).left x ((LPow A L a T).U j)
      (chart_le_res A L (g ▷ A) (whiskerRight_snd g A) a j
        (show (ptSecT A (g ≫ z)).left x ∈ (LPow A L a T').U j from hPgz)),
    ptSecT_whisker, ← gs_pull g.left (ptSecT A z).left x _ hPz, ← gs_res _ x (val_le A L z j) hx',
    hv j, gs_mul _ x _ hx', gs_res _ x le_top hx']

  erw [gs_mul _ x _ hx, gs_res _ x le_top hx, gs_pull (𝟙 T'.left) g.left x ⊤ (by simp), Category.id_comp]
  congr 1
  dsimp only
  show gs g.left x (LB.wchart L (fun _ : Fin 1 => z.left) j) (τ.s j).val =
    gs (𝟙 _) x _ (((T'.left.presheaf.map (homOfLE _).op).hom ((g.left.app _).hom (τ.s j).val)))
  erw [gs_res _ x _ hx, gs_pull (𝟙 _) g.left x _ hx', Category.id_comp]
end Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
