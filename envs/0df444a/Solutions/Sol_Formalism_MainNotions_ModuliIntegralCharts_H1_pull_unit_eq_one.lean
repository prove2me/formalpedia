-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.pull_unit_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:28:05.925107+00:00
-- url     : https://prove2.me/submissions/de241a08-46ac-45f6-a296-55ac11ab9d21

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_pull_restrict_unit_value

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
open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution {X Y S0 : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : S0 ⟶ Y) (ψ : S0 ⟶ X)
    (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => 1))
    (t t' : LB.Gen (LB.LinComb L φ ε)) (u : Γ(Y, ⊤)ˣ)
    (hu : ∀ j, t.s j = res (le_top : (LB.LinComb L φ ε).U j ≤ ⊤) u * t'.s j)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t h) rig)
    (hc' : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t' h) rig) :
    (h.app ⊤).hom (u : Γ(Y, ⊤)) = 1 := by
  classical
  have hpt : ∀ (m : S0 ⟶ X) (z : S0), ∃ i, m.base z ∈ L.U i := fun m z => by
    have hz : m.base z ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using hz
  let c : S0 → (S0 ⟶ X) → L.ι := fun z m =>
    if m = ψ then (hpt ψ z).choose else (hpt m z).choose
  have hc_mem : ∀ z m, m.base z ∈ L.U (c z m) := by
    intro z m
    simp only [c]
    split_ifs with hm
    · subst hm; exact (hpt _ z).choose_spec
    · exact (hpt m z).choose_spec
  let j : S0 → K → L.ι := fun z k => c z (h ≫ φ k)
  let j' : S0 → PUnit → L.ι := fun z _ => c z ψ
  let W : S0 → S0.Opens := fun z =>
    LB.wchart L (fun k => h ≫ φ k) (j z) ⊓ LB.wchart L (fun _ : PUnit => ψ) (j' z)
  have hzW : ∀ z, z ∈ W z := fun z =>
    ⟨Set.mem_iInter.2 fun k => hc_mem z _, Set.mem_iInter.2 fun _ => hc_mem z ψ⟩
  have hone : ∀ z, (S0.presheaf.map (homOfLE (le_top : W z ≤ h ⁻¹ᵁ ⊤)).op).hom
      ((h.app ⊤).hom (u : Γ(Y, ⊤))) = 1 := by
    intro z
    have hcoh : LB.Coh L (fun k => h ≫ φ k) (j z) := fun k1 k2 e => congrArg (c z) e
    have hcoh' : LB.Coh L (fun _ : PUnit => ψ) (j' z) := fun _ _ _ => rfl
    have hcomp : ∀ k k', (fun k => h ≫ φ k) k = (fun _ : PUnit => ψ) k' → j z k = j' z k' :=
      fun k k' e => congrArg (c z) e
    have e := (hc (j z) (j' z) hcoh hcoh' hcomp).trans (hc' (j z) (j' z) hcoh hcoh' hcomp).symm
    simp only [LB.pullGen] at e
    rw [hu (j z)] at e
    simp only [map_mul] at e
    erw [map_mul] at e
    have e2 := mul_eq_right.mp e
    have e3 := congrArg Units.val e2
    have hWV : LB.wchart L (fun k => h ≫ φ k) (j z) ≤ h ⁻¹ᵁ LB.wchart L φ (j z) :=
      fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
    exact (pull_restrict_unit_value h (W' := W z) hWV inf_le_left u).symm.trans (e3.trans Units.val_one)
  refine S0.sheaf.eq_of_locally_eq' W (h ⁻¹ᵁ ⊤) (fun z => homOfLE le_top) ?_ _ _ ?_
  · intro z _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨z, hzW z⟩
  · intro z
    change (S0.presheaf.map (homOfLE (le_top : W z ≤ h ⁻¹ᵁ ⊤)).op).hom
      ((h.app ⊤).hom (u : Γ(Y, ⊤))) = (S0.presheaf.map (homOfLE (le_top : W z ≤ h ⁻¹ᵁ ⊤)).op).hom 1
    rw [hone z, map_one]
end Formalism.MainNotions.ModuliIntegralCharts.H1
