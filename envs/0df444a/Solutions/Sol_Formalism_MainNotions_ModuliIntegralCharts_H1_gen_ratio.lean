-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.gen_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:51.929394+00:00
-- url     : https://prove2.me/submissions/4d9f25d9-6f57-4555-8706-0183eb877268

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PrimUniqPf

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
theorem _root_.solution {Y : Scheme.{0}} (M : LB Y) (hcov : (⊤ : Y.Opens) ≤ ⨆ j, M.U j)
    (t t' : LB.Gen M) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ u : Γ(Y, ⊤)ˣ, ∀ j, t.s j = res (le_top : M.U j ≤ ⊤) u * t'.s j := by
  classical
  let r : ∀ j, Γ(Y, M.U j)ˣ := fun j => t.s j / t'.s j
  have hcompat : ∀ i j, res (inf_le_left : M.U i ⊓ M.U j ≤ M.U i) (r i) =
      res (inf_le_right : M.U i ⊓ M.U j ≤ M.U j) (r j) := by
    intro i j
    simp only [r, map_div, ht i j, ht' i j, mul_div_mul_left_eq_div]
  have hcompat' : ∀ i j, res (inf_le_left : M.U i ⊓ M.U j ≤ M.U i) (r i)⁻¹ =
      res (inf_le_right : M.U i ⊓ M.U j ≤ M.U j) (r j)⁻¹ := by
    intro i j
    rw [map_inv, map_inv, hcompat i j]
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' M.U ⊤ (fun j => homOfLE le_top) hcov
    (fun j => ((r j : Γ(Y, M.U j)ˣ) : Γ(Y, M.U j))) (fun i j => congrArg Units.val (hcompat i j))
  obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' M.U ⊤ (fun j => homOfLE le_top) hcov
    (fun j => (((r j)⁻¹ : Γ(Y, M.U j)ˣ) : Γ(Y, M.U j))) (fun i j => congrArg Units.val (hcompat' i j))
  have hab : a * b = 1 := by
    refine Y.sheaf.eq_of_locally_eq' M.U ⊤ (fun j => homOfLE le_top) hcov _ _ fun j => ?_
    change (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom (a * b) =
      (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom 1
    erw [map_mul, map_one]
    have e1 := ha j
    have e2 := hb j
    change (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom a = ((r j : Γ(Y, M.U j)ˣ) : Γ(Y, M.U j)) at e1
    change (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom b =
      (((r j)⁻¹ : Γ(Y, M.U j)ˣ) : Γ(Y, M.U j)) at e2
    rw [e1, e2, Units.mul_inv]
  refine ⟨⟨a, b, hab, by erw [mul_comm]; exact hab⟩, fun j => ?_⟩
  have hres : res (le_top : M.U j ≤ ⊤) ⟨a, b, hab, by erw [mul_comm]; exact hab⟩ = r j :=
    Units.ext (ha j)
  rw [hres]
  simp only [r, div_mul_cancel]
end Formalism.MainNotions.ModuliIntegralCharts.H1
