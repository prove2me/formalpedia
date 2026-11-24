-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.scaled_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:46:52.974832+00:00
-- url     : https://prove2.me/submissions/b29c9b5f-1adb-40f4-b1b6-dc4233be7bcc

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqH
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
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
theorem _root_.solution {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) {u v : Γ(Y, ⊤)ˣ} {t t' : LB.Gen (LB.LinComb L φ ε)}
    {s s' : LB.Gen (LB.LinComb L φ' ε')} (h1 : IsScaled u t t') (h2 : IsScaled v s s') :
    IsScaled (u * v) (LB.mulGen L φ ε φ' ε' t s) (LB.mulGen L φ ε φ' ε' t' s') := by
  have h1' : ∀ j, t'.s j = res le_top u * t.s j := h1
  have h2' : ∀ j, s'.s j = res le_top v * s.s j := h2
  intro j
  simp only [LB.mulGen]
  erw [h1' (j ∘ Sum.inl), h2' (j ∘ Sum.inr)]
  simp only [map_mul]
  erw [res_res, res_res]
  rw [mul_mul_mul_comm]
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
