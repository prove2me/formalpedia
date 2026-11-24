-- Prove2me | solution 1 for Formalism.L2.Pj.intFrames_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:40.59111+00:00
-- url     : https://prove2.me/submissions/09639129-1f32-4450-a079-1d6d65000578

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntFrames
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabPull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
set_option maxHeartbeats 1000000
namespace Formalism.L2.Pj
theorem _root_.solution (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) (hG : GenFibreSt Xo c) (hL : LieFreeSt Xo c)
    (hT : ThetaFrameSt Xo c) (hS : SpreadSt Xo c) : IntFramesSt Xo c := by

  have e : ∀ (X : Scheme.{0}) (U : X.Opens) (h : U ≤ (𝟙 X) ⁻¹ᵁ U) (v : Γ(X, U)),
      (Scheme.Hom.appLE (𝟙 X) U U h).hom v = v := by
    intro X U h v
    simp [Scheme.Hom.appLE]
    first
      | (erw [Category.id_comp, CategoryTheory.Functor.map_id]; rfl)
      | (erw [Category.id_comp, CategoryTheory.Functor.map_id]; simp; done)
      | (erw [CategoryTheory.Functor.map_id]; simp; done)
  have key : ∀ {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s s0 : LB.Sec (PPx x)) (a : S),
      (∀ i, s.f i = scal x a i * s0.f i) → ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι)
        (h : (PPx x).U i ≤ (𝟙 (Gx x)) ⁻¹ᵁ (PPx x).U i),
        (Scheme.Hom.appLE (𝟙 (Gx x)) _ _ h).hom (scal x a i * s0.f i) = s.f i := by
    intro S _ x s s0 a ha i h
    rw [ha i]
    exact e _ _ _ _
  intro T io O _ β Y hP yt z h1 h2
  letI := io.toAlgebra
  intro y₀ hy₀
  obtain ⟨x0, hx0, u0, tan0, eig0, basis0, s0, gen0⟩ := y₀
  dsimp only at hy₀
  subst hy₀
  obtain ⟨PP', cub, sym, adj, prim, mG, -⟩ := sabPull hC yt Y.t
  obtain ⟨t', m1, m2, -⟩ := hG T io O β Y yt z h1 h2 _ mG
  obtain ⟨ub, u, ⟨hub1, hub2, hub3, hub4⟩, hu1, hu2, hu3, hu4⟩ :=
    hL T io _ t' _ m1 m2 hx0 u0 tan0 eig0 basis0
  obtain ⟨θ, s, hθ1, hθ2, hs, a, ha⟩ := hT T io O β Y hP yt z h1 h2 _ mG t' m1 m2 s0 gen0
  choose cf hcf1 hcf2 hcf3 using hu4
  let y : FrPt Xo c T.Fr :=
    { x := _, x_over := hx0, u := u, tan := hu1, eig := hu2, basis := hu3, s := s, gen := hs }
  refine ⟨⟨y, hS T.Fr y, _, t', m1, m2, ⟨ub, hub1, hub2, hub3, hub4⟩, θ, hθ1, hθ2⟩,
    fun k => match k with | none => a | some p => (hcf1 p.1 p.2).unit, rfl, ?_, 𝟙 _, ?_, ?_, ?_⟩
  · intro τ i
    exact ⟨cf τ i, (hcf1 τ i).unit_spec.symm, hcf2 τ i, hcf3 τ i⟩
  · exact Category.id_comp _
  · exact Category.id_comp _
  · exact key _ s s0 _ ha
end Formalism.L2.Pj
