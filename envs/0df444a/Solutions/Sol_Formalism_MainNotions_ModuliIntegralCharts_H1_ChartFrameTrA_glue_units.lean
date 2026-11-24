-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.glue_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:00:10.615002+00:00
-- url     : https://prove2.me/submissions/b861377f-529f-4a5f-b837-9f5c4df813f9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartFrameTrA

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
theorem _root_.solution {X : Scheme.{0}} {κ : Type} (U : κ → X.Opens) (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (r : ∀ i, Γ(X, U i)ˣ)
    (hr : ∀ i j, res (inf_le_left : U i ⊓ U j ≤ U i) (r i) = res (inf_le_right : U i ⊓ U j ≤ U j) (r j)) :
    ∃ u : Γ(X, ⊤)ˣ, ∀ i, res (le_top : U i ≤ ⊤) u = r i := by
  simp only [res] at hr ⊢
  have hc : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    obtain ⟨i, hi⟩ := hcov x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  obtain ⟨s, hs, -⟩ : ∃! s : Γ(X, ⊤), ∀ i,
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom s = (r i : Γ(X, U i)) :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hc
    (fun i => ((r i : Γ(X, U i)))) (fun i j => by
      have h1 := congrArg Units.val (hr i j)
      simp only [Units.coe_map, MonoidHom.coe_coe] at h1
      exact h1)
  obtain ⟨t, ht, -⟩ : ∃! t : Γ(X, ⊤), ∀ i,
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom t = (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hc
    (fun i => (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i))) (fun i j => by
      have h1 := congrArg (fun v => ((v⁻¹ : Γ(X, U i ⊓ U j)ˣ) : Γ(X, U i ⊓ U j))) (hr i j)
      simp only [← map_inv, Units.coe_map, MonoidHom.coe_coe] at h1
      exact h1)
  have hs' : ∀ i, (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom s = (r i : Γ(X, U i)) :=
    fun i => hs i
  have ht' : ∀ i, (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom t =
      (((r i)⁻¹ : Γ(X, U i)ˣ) : Γ(X, U i)) := fun i => ht i
  have hst : s * t = 1 := by
    apply X.sheaf.eq_of_locally_eq' U ⊤ (fun i => homOfLE le_top) hc
    intro i
    show (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom (s * t) =
      (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom 1
    rw [map_mul, map_one, hs' i, ht' i, Units.mul_inv]
  refine ⟨⟨s, t, hst, by rw [mul_comm]; exact hst⟩, fun i => ?_⟩
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mk]
  exact hs' i
end Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA
