-- Prove2me | solution 1 for DiscreteConvex.LConvexSets.lconvex_intersection_properties
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T07:57:02.477469+00:00
-- url     : https://prove2.me/submissions/fcb352fb-05b0-4244-8d16-10904475a874

import Definitions.Def_DiscreteConvex_LConvexSets_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexSets_ConvexClosureSet
import Theorems.Thm_DiscreteConvex_LConvexSetsB_lconvex_integrally_convex


set_option autoImplicit false
namespace LIntersectionPublic
open DiscreteConvex.LConvexSets
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem asB (D : Set (V → ℤ)) (hD : LConvexSet D) (hne : D.Nonempty) :
    DiscreteConvex.LConvexSetsB.LConvexSet D := ⟨hne,hD.1,hD.2⟩

theorem nonempty_of_hull (D : Set (V → ℤ)) (p : V → ℝ)
    (hp : p ∈ ConvexClosureSet D) : D.Nonempty := by
  by_contra h
  have he : D=∅ := Set.not_nonempty_iff_eq_empty.mp h
  simp [ConvexClosureSet,he] at hp

theorem intersection_closed (D1 D2 : Set (V → ℤ))
    (h1 : LConvexSet D1) (h2 : LConvexSet D2) : LConvexSet (D1 ∩ D2) := by
  constructor
  · intro p hp q hq
    exact ⟨⟨(h1.1 p hp.1 q hq.1).1,(h2.1 p hp.2 q hq.2).1⟩,
      ⟨(h1.1 p hp.1 q hq.1).2,(h2.1 p hp.2 q hq.2).2⟩⟩
  · intro p hp
    exact ⟨⟨(h1.2 p hp.1).1,(h2.2 p hp.2).1⟩,
      ⟨(h1.2 p hp.1).2,(h2.2 p hp.2).2⟩⟩

theorem hull_intersection (D1 D2 : Set (V → ℤ))
    (h1 : LConvexSet D1) (h2 : LConvexSet D2) :
    ConvexClosureSet D1 ∩ ConvexClosureSet D2 = ConvexClosureSet (D1 ∩ D2) := by
  ext p
  constructor
  · rintro ⟨hp1,hp2⟩
    have hb1 := asB D1 h1 (nonempty_of_hull D1 p hp1)
    have hb2 := asB D2 h2 (nonempty_of_hull D2 p hp2)
    have hn1 : ∀ i ≤ (DiscreteConvex.LConvexSetsB.FracSortedValues p).length,
        DiscreteConvex.LConvexSetsB.NeighborVec p i ∈ D1 := by
      change p ∈ convexHull ℝ (DiscreteConvex.LConvexSetsB.IntEmbed D1) at hp1
      rwa [(DiscreteConvex.LConvexSetsB.lconvex_integrally_convex D1 hb1).1] at hp1
    have hn2 : ∀ i ≤ (DiscreteConvex.LConvexSetsB.FracSortedValues p).length,
        DiscreteConvex.LConvexSetsB.NeighborVec p i ∈ D2 := by
      change p ∈ convexHull ℝ (DiscreteConvex.LConvexSetsB.IntEmbed D2) at hp2
      rwa [(DiscreteConvex.LConvexSetsB.lconvex_integrally_convex D2 hb2).1] at hp2
    have hne : (D1 ∩ D2).Nonempty :=
      ⟨DiscreteConvex.LConvexSetsB.NeighborVec p 0, hn1 0 (Nat.zero_le _), hn2 0 (Nat.zero_le _)⟩
    change p ∈ convexHull ℝ (DiscreteConvex.LConvexSetsB.IntEmbed (D1 ∩ D2))
    rw [(DiscreteConvex.LConvexSetsB.lconvex_integrally_convex (D1 ∩ D2)
      (asB _ (intersection_closed D1 D2 h1 h2) hne)).1]
    exact fun i hi => ⟨hn1 i hi,hn2 i hi⟩
  · intro hp
    constructor
    · exact convexHull_mono (Set.image_mono Set.inter_subset_left) hp
    · exact convexHull_mono (Set.image_mono Set.inter_subset_right) hp


end LIntersectionPublic

open DiscreteConvex.LConvexSets

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (D1 D2 : Set (V → ℤ)) (hD1 : LConvexSet D1) (hD2 : LConvexSet D2) :
    ConvexClosureSet D1 ∩ ConvexClosureSet D2 = ConvexClosureSet (D1 ∩ D2) ∧
      ((D1 ∩ D2).Nonempty → LConvexSet (D1 ∩ D2)) := by
  exact ⟨LIntersectionPublic.hull_intersection D1 D2 hD1 hD2, fun _ => LIntersectionPublic.intersection_closed D1 D2 hD1 hD2⟩

#print axioms solution
