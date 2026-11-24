-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.corr_scaled_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:46:51.637172+00:00
-- url     : https://prove2.me/submissions/c2c88f77-3794-4b5e-9795-9a3345236b60

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqH
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_gen_eq_of_corr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_res_res


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
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
variable {X Y Z : Scheme.{0}} (L : LB X)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
theorem _root_.solution (hL : L.IsLB) (ψ : Y ⟶ X) (a : ℤ) {K' : Type} [Fintype K'] (φ' : K' → (Y ⟶ X))
    (ε' : K' → ℤ) (τ τ' : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => ψ) fun _ => a))
    (t₂ t₂' : LB.Gen (LB.LinComb L φ' ε')) (U : Γ(Y, ⊤)ˣ) (h₂ : IsScaled U t₂ t₂')
    (c : LB.Gen.Corr L _ _ _ _ τ t₂) (c' : LB.Gen.Corr L _ _ _ _ τ' t₂') : IsScaled U τ τ' := by
  let τ'' : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => ψ) fun _ => a) :=
    ⟨fun j => res le_top U * τ.s j⟩
  have h₂' : ∀ j, t₂'.s j = res le_top U * t₂.s j := h₂
  have hc'' : LB.Gen.Corr L _ _ _ _ τ'' t₂' := by
    intro j j' hj hj' hm
    have := c j j' hj hj' hm
    show res _ (res le_top U * τ.s j) = res _ (t₂'.s j')
    rw [h₂' j']
    erw [map_mul, map_mul, this, res_res, res_res]
    rfl
  have he := GermFun.gen_eq_of_corr L hL ψ a φ' ε' τ'' τ' t₂' hc'' c'
  intro j
  rw [← he]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
