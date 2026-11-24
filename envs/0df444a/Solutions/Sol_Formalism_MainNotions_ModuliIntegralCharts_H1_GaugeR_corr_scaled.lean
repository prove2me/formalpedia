-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.corr_scaled
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:46:50.531745+00:00
-- url     : https://prove2.me/submissions/da7bb66f-8c15-48d3-b115-5404424a2c26

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqH
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_res_res
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_wchart_cover


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
theorem _root_.solution (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t₁ t₁' : LB.Gen (LB.LinComb L φ ε))
    (t₂ t₂' : LB.Gen (LB.LinComb L φ' ε')) (U₁ U₂ : Γ(Y, ⊤)ˣ) (h₁ : IsScaled U₁ t₁ t₁')
    (h₂ : IsScaled U₂ t₂ t₂') (c : LB.Gen.Corr L φ ε φ' ε' t₁ t₂) (c' : LB.Gen.Corr L φ ε φ' ε' t₁' t₂') :
    U₁ = U₂ := by
  classical
  have h₁' : ∀ j, t₁'.s j = res le_top U₁ * t₁.s j := h₁
  have h₂' : ∀ j, t₂'.s j = res le_top U₂ * t₂.s j := h₂
  have key : ∀ {U V : Y.Opens} (hle : V ≤ U) (a b : Γ(Y, U)ˣ), res hle (a * b) = res hle a * res hle b :=
    fun hle a b => map_mul _ a b
  have hch : ∀ (ψ : Y ⟶ X) (y : Y), ∃ i, ψ y ∈ L.U i := by
    intro ψ y
    have hy := wchart_cover L hL (fun _ : Fin 1 => ψ) (show y ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact ⟨j 0, Set.mem_iInter.1 hj 0⟩
  apply Units.ext
  have hcov : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧
      (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (U₁ : Γ(Y, ⊤)) =
        (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (U₂ : Γ(Y, ⊤)) := by
    intro y
    choose ch hc using fun ψ => hch ψ y
    let j : K → L.ι := fun k => ch (φ k)
    let j' : K' → L.ι := fun k => ch (φ' k)
    have hj : LB.Coh L φ j := fun k1 k2 e => show ch (φ k1) = ch (φ k2) by rw [e]
    have hj' : LB.Coh L φ' j' := fun k1 k2 e => show ch (φ' k1) = ch (φ' k2) by rw [e]
    have hjj : ∀ k k', φ k = φ' k' → j k = j' k' := fun k k' e => show ch (φ k) = ch (φ' k') by rw [e]
    have hyW : y ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' :=
      ⟨Set.mem_iInter.2 fun k => hc (φ k), Set.mem_iInter.2 fun k => hc (φ' k)⟩
    have E := c j j' hj hj' hjj
    have E' := c' j j' hj hj' hjj
    rw [h₁' j, h₂' j'] at E'
    erw [key, key, res_res, res_res, E] at E'
    have E2 := mul_right_cancel E'
    exact ⟨_, hyW, congrArg Units.val E2⟩
  choose W hyW hW using hcov
  exact TopCat.Sheaf.eq_of_locally_eq' Y.sheaf W ⊤ (fun y => homOfLE le_top)
    (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyW y⟩) _ _ hW
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
