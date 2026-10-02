-- Prove2me | solution 1 for DiscreteConvex.LConvexSets.hole_free_lconvex
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T07:57:25.766512+00:00
-- url     : https://prove2.me/submissions/fb81a51d-a81a-4395-920b-309071f49a4f

import Definitions.Def_DiscreteConvex_LConvexSets_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexSets_ConvexClosureSet
import Theorems.Thm_DiscreteConvex_LConvexSetsB_lconvex_integrally_convex


set_option autoImplicit false
namespace LHoleFreePublic
open DiscreteConvex.LConvexSets
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem asB (D : Set (V → ℤ)) (hD : LConvexSet D) (hne : D.Nonempty) :
    DiscreteConvex.LConvexSetsB.LConvexSet D := ⟨hne,hD.1,hD.2⟩

theorem nonempty_of_hull (D : Set (V → ℤ)) (p : V → ℝ)
    (hp : p ∈ ConvexClosureSet D) : D.Nonempty := by
  by_contra h
  have he : D=∅ := Set.not_nonempty_iff_eq_empty.mp h
  simp [ConvexClosureSet,he] at hp

theorem hole_free (D : Set (V → ℤ)) (hD : LConvexSet D) (p : V → ℤ) :
    p ∈ D ↔ (fun v => (p v : ℝ)) ∈ ConvexClosureSet D := by
  constructor
  · intro hp
    exact subset_convexHull ℝ _ ⟨p,hp,rfl⟩
  · intro hp
    have hb := asB D hD (nonempty_of_hull D _ hp)
    change (fun v => (p v : ℝ)) ∈ convexHull ℝ (DiscreteConvex.LConvexSetsB.IntEmbed D) at hp
    rw [(DiscreteConvex.LConvexSetsB.lconvex_integrally_convex D hb).1] at hp
    have hh := hp 0 (Nat.zero_le _)
    have he : DiscreteConvex.LConvexSetsB.NeighborVec (fun v => (p v : ℝ)) 0 = p := by
      classical
      funext v
      simp [DiscreteConvex.LConvexSetsB.NeighborVec,DiscreteConvex.LConvexSetsB.FracLevelSet]
    exact he ▸ hh


end LHoleFreePublic

open DiscreteConvex.LConvexSets

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (D : Set (V → ℤ))
    (hD : LConvexSet D) :
    ∀ p : V → ℤ, p ∈ D ↔ (fun v => (p v : ℝ)) ∈ ConvexClosureSet D := by
  exact fun p => LHoleFreePublic.hole_free D hD p

#print axioms solution
