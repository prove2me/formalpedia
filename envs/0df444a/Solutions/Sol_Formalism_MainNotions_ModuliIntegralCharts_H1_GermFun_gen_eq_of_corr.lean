-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.gen_eq_of_corr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:09.096638+00:00
-- url     : https://prove2.me/submissions/d5787bac-7a29-425f-8b43-37e8969037e1

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
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (ψ : Y ⟶ X) (a : ℤ) {K' : Type}
    [Fintype K'] (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t₁ t₂ : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => ψ) fun _ => a))
    (g : LB.Gen (LB.LinComb L φ' ε')) (h₁ : LB.Gen.Corr L _ _ _ _ t₁ g)
    (h₂ : LB.Gen.Corr L _ _ _ _ t₂ g) : t₁ = t₂ := by
  classical
  unfold LB.Gen.Corr at h₁ h₂
  obtain ⟨s₁⟩ := t₁
  obtain ⟨s₂⟩ := t₂
  congr 1
  funext j
  apply Units.ext
  have coh1 : L.Coh (fun _ : Fin 1 => ψ) j := fun k₁ k₂ _ => congrArg j (Subsingleton.elim k₁ k₂)
  refine sec_eq_of_cover (X := Y)
    (fun j' : {j' : K' → L.ι // L.Coh φ' j' ∧ ∀ (k : Fin 1) (k' : K'), ψ = φ' k' → j k = j' k'} =>
      (LB.LinComb L (K := Fin 1) (fun _ => ψ) fun _ => a).U j ⊓ (LB.LinComb L φ' ε').U j'.1)
    (fun _ => inf_le_left) ?_ _ _ (fun j' => ?_)
  · intro p hp
    have hp' : p ∈ L.wchart (fun _ : Fin 1 => ψ) j := hp
    unfold LB.wchart at hp'
    rw [TopologicalSpace.Opens.mem_mk, Set.mem_iInter] at hp'
    have hψ : ψ p ∈ L.U (j 0) := hp' 0
    let c : (Y ⟶ X) → L.ι := fun φ =>
      if φ = ψ then j 0 else Classical.choose (exists_chart L hL (φ p))
    have hc : ∀ φ : Y ⟶ X, φ p ∈ L.U (c φ) := by
      intro φ
      by_cases hφ : φ = ψ
      · simp only [c, if_pos hφ]
        rw [hφ]
        exact hψ
      · simp only [c, if_neg hφ]
        exact Classical.choose_spec (exists_chart L hL (φ p))
    have hcoh : L.Coh φ' (fun k' => c (φ' k')) := fun k₁ k₂ h => congrArg c h
    have hcomp : ∀ (k : Fin 1) (k' : K'), ψ = φ' k' → j k = c (φ' k') := by
      intro k k' hk
      rw [← hk, Subsingleton.elim k 0]
      simp only [c, if_pos rfl]
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨⟨fun k' => c (φ' k'), hcoh, hcomp⟩, hp, ?_⟩
    show p ∈ L.wchart φ' (fun k' => c (φ' k'))
    unfold LB.wchart
    rw [TopologicalSpace.Opens.mem_mk, Set.mem_iInter]
    intro k'
    exact hc (φ' k')
  · have e := (h₁ j j'.1 coh1 j'.2.1 j'.2.2).trans (h₂ j j'.1 coh1 j'.2.1 j'.2.2).symm
    have e2 := congrArg Units.val e
    exact e2
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
