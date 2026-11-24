-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.exists_ratio_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:26:44.71883+00:00
-- url     : https://prove2.me/submissions/a7f1d8d4-af8b-4a6d-9b2a-fe0b88b76e09

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartFrameTrA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ChartFrameTrA_glue_units

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA
theorem _root_.solution {X : Scheme.{0}} {M : LB X} (hcov : ∀ x : X, ∃ i, x ∈ M.U i) {g₁ g₂ : LB.Gen M}
    (h₁ : g₁.IsGen) (h₂ : g₂.IsGen) : ∃ u : Γ(X, ⊤)ˣ, ∀ i, g₁.s i = res (le_top : M.U i ≤ ⊤) u * g₂.s i := by
  unfold LB.Gen.IsGen at h₁ h₂
  obtain ⟨u, hu⟩ := glue_units M.U hcov (fun i => g₁.s i / g₂.s i) (fun i j => by
    rw [map_div, map_div, h₁ i j, h₂ i j, mul_div_mul_left_eq_div])
  exact ⟨u, fun i => by rw [hu i, div_mul_cancel]⟩
end Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA
