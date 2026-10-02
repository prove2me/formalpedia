-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityC.prop_3_17_holefree_intersection_minkowski_relations
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:36:45.281059+00:00
-- url     : https://prove2.me/submissions/6ee754dc-e34c-4c83-abcf-6b6df21cd621

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_HoleFree
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ConvexClosureSet
import Definitions.Def_DiscreteConvex_IntegralConvexityC_MinkowskiSumZ
import Definitions.Def_DiscreteConvex_IntegralConvexityC_EmbedZR

set_option autoImplicit false

open DiscreteConvex.IntegralConvexityC Pointwise in
theorem faa60660_image_minkowski {n : ℕ} (S1 S2 : Set (Fin n → ℤ)) :
    EmbedZR '' MinkowskiSumZ S1 S2 = EmbedZR '' S1 + EmbedZR '' S2 := by
  ext y
  simp only [Set.mem_image, MinkowskiSumZ, Set.mem_ofPred_eq, Set.mem_add]
  constructor
  · rintro ⟨x, ⟨x1, hx1, x2, hx2, rfl⟩, rfl⟩
    refine ⟨EmbedZR x1, ⟨x1, hx1, rfl⟩, EmbedZR x2, ⟨x2, hx2, rfl⟩, ?_⟩
    funext i
    simp [EmbedZR]
  · rintro ⟨a, ⟨x1, hx1, rfl⟩, b, ⟨x2, hx2, rfl⟩, rfl⟩
    refine ⟨x1 + x2, ⟨x1, hx1, x2, hx2, rfl⟩, ?_⟩
    funext i
    simp [EmbedZR]

open DiscreteConvex.IntegralConvexityC Pointwise in
theorem solution {n : ℕ} (S1 S2 : Set (Fin n → ℤ))
    (h1 : HoleFree S1) (h2 : HoleFree S2) :
    (ConvexClosureSet S1 ∩ ConvexClosureSet S2 ⊇ ConvexClosureSet (S1 ∩ S2)) ∧
      (S1 ∩ S2 = {x : Fin n → ℤ | EmbedZR x ∈ ConvexClosureSet S1 ∩ ConvexClosureSet S2}) ∧
      (MinkowskiSumZ S1 S2 ⊆
          {x : Fin n → ℤ | EmbedZR x ∈ ConvexClosureSet S1 + ConvexClosureSet S2}) ∧
      (ConvexClosureSet (MinkowskiSumZ S1 S2) =
        ConvexClosureSet S1 + ConvexClosureSet S2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Set.subset_inter
      (convexHull_mono (Set.image_mono Set.inter_subset_left))
      (convexHull_mono (Set.image_mono Set.inter_subset_right))
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [h1 x, h2 x]
  · rintro x ⟨x1, hx1, x2, hx2, rfl⟩
    refine Set.mem_ofPred_eq ▸ ?_
    have hx : EmbedZR (x1 + x2) = EmbedZR x1 + EmbedZR x2 := by
      funext i; simp [EmbedZR]
    rw [hx]
    exact Set.add_mem_add (subset_convexHull ℝ _ ⟨x1, hx1, rfl⟩)
      (subset_convexHull ℝ _ ⟨x2, hx2, rfl⟩)
  · unfold ConvexClosureSet
    rw [faa60660_image_minkowski, convexHull_add]
