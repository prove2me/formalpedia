-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.value_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:14.266592+00:00
-- url     : https://prove2.me/submissions/fe1be87d-447c-4e07-8113-aae689155645

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFun
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_sec_eq_of_cover
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_exists_chart

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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
theorem _root_.solution {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (hL : L.IsLB) (a : ℤ)
    {T : Over S} (s : LB.Sec (LPow A L a T)) (z : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)))
    (v₁ v₂ : Γ(T.left, ⊤)) (h₁ : IsValueAt A L a s z τ v₁) (h₂ : IsValueAt A L a s z τ v₂) : v₁ = v₂ := by
  refine sec_eq_of_cover (V := fun j => (L.LinComb (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j)
    (fun j => le_top) ?_ v₁ v₂ (fun j => ?_)
  · intro p _
    obtain ⟨i, hi⟩ := exists_chart L hL (z.left p)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨fun _ => i, ?_⟩
    show p ∈ L.wchart (fun _ : Fin 1 => z.left) (fun _ => i)
    unfold LB.wchart
    rw [TopologicalSpace.Opens.mem_mk, Set.mem_iInter]
    intro _
    exact hi
  · have h3 := (h₁ j).symm.trans (h₂ j)
    exact (Units.mul_left_inj (τ.s j)).1 h3
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
