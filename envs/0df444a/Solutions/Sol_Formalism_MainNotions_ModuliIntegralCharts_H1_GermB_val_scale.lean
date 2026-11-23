-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.val_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:22.152148+00:00
-- url     : https://prove2.me/submissions/3af6986a-82e3-4f58-abce-d3ee964db80f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
theorem _root_.solution {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι)
    (hJ : Good t.PP.L z J) : val (scaleGenG t φ ε u g) r z J = gm r z ⊤ u * val g r z J := by
  unfold scaleGenG val gm
  have hz : r z ∈ t.PP.L.wchart φ fun k => J (r ≫ φ k) := by
    unfold Good at hJ
    unfold LB.wchart
    show r z ∈ (⋂ k, ⇑(φ k) ⁻¹' ↑(t.PP.L.U (J (r ≫ φ k))) : Set _)
    rw [Set.mem_iInter]
    intro k
    have hk := hJ (r ≫ φ k)
    simpa using hk
  rw [dif_pos hz, dif_pos (show r z ∈ (⊤ : Y.Opens) from trivial)]
  dsimp only
  refine (MonoidHom.map_mul _ _ _).trans ?_
  congr 1
  apply Units.ext
  unfold pullU res
  have hz' : z ∈ r ⁻¹ᵁ (t.PP.L.wchart φ fun k => J (r ≫ φ k)) := hz
  have ht : z ∈ r ⁻¹ᵁ (⊤ : Y.Opens) := trivial
  have key := congrArg (fun f => CommRingCat.Hom.hom f (u : Γ(Y, ⊤)))
    (show Y.presheaf.map (homOfLE (le_top : t.PP.L.wchart φ (fun k => J (r ≫ φ k)) ≤ ⊤)).op ≫
        Scheme.Hom.app r (t.PP.L.wchart φ fun k => J (r ≫ φ k)) ≫
        Z.presheaf.germ (r ⁻¹ᵁ t.PP.L.wchart φ fun k => J (r ≫ φ k)) z hz' =
        Scheme.Hom.app r ⊤ ≫ Z.presheaf.germ (r ⁻¹ᵁ ⊤) z ht by
      rw [Scheme.Hom.naturality_assoc, TopCat.Presheaf.germ_res]
      all_goals rfl)
  first
    | exact key
    | (simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key
       simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
       exact key)
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
