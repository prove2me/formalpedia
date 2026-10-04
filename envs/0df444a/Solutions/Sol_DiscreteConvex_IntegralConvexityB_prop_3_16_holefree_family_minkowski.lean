-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityB.prop_3_16_holefree_family_minkowski
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:32:02.565128+00:00
-- url     : https://prove2.me/submissions/34b1b2a4-4637-401a-837d-bbfd7d0195df

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsTranslInvariantHoleFreeFamily
import Definitions.Def_DiscreteConvex_IntegralConvexityB_ConvexClosureSet
import Definitions.Def_DiscreteConvex_IntegralConvexityB_MinkowskiSumZ
import Definitions.Def_DiscreteConvex_IntegralConvexityB_EmbedZR

open DiscreteConvex.IntegralConvexityB
open scoped Pointwise

namespace HoleFreeMinkowskiCore

/-- The affine map `z ↦ a - z`. -/
noncomputable def reflMap {V : Type*} (a : V → ℝ) : (V → ℝ) →ᵃ[ℝ] (V → ℝ) :=
  AffineMap.const ℝ (V → ℝ) a - AffineMap.id ℝ (V → ℝ)

lemma reflMap_apply {V : Type*} (a z : V → ℝ) : reflMap a z = a - z := by
  simp [reflMap]

/-- The convex closure of the reflected translate `x - S` is `x - S̄`. -/
lemma closure_refl {V : Type*} (x : V → ℤ) (S : Set (V → ℤ)) :
    ConvexClosureSet ((fun y => x - y) '' S) = (reflMap (EmbedZR x)) '' ConvexClosureSet S := by
  unfold ConvexClosureSet
  rw [AffineMap.image_convexHull]
  congr 1
  ext z
  simp only [Set.mem_image]
  constructor
  · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨EmbedZR y, ⟨y, hy, rfl⟩, ?_⟩
    rw [reflMap_apply]; funext v; simp [EmbedZR]
  · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨x - y, ⟨y, hy, rfl⟩, ?_⟩
    rw [reflMap_apply]; funext v; simp [EmbedZR]

lemma embed_mem_closure {V : Type*} {S : Set (V → ℤ)} {y : V → ℤ} (hy : y ∈ S) :
    EmbedZR y ∈ ConvexClosureSet S :=
  subset_convexHull ℝ _ ⟨y, hy, rfl⟩

end HoleFreeMinkowskiCore

open HoleFreeMinkowskiCore in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (F : Set (Set (V → ℤ))) (hF : IsTranslInvariantHoleFreeFamily F) :
    (∀ S1 ∈ F, ∀ S2 ∈ F, S1 ∩ S2 = ∅ → ConvexClosureSet S1 ∩ ConvexClosureSet S2 = ∅) ↔
      (∀ S1 ∈ F, ∀ S2 ∈ F,
        MinkowskiSumZ S1 S2 =
          {x : V → ℤ | EmbedZR x ∈ ConvexClosureSet S1 + ConvexClosureSet S2}) := by
  constructor
  · intro ha S1 hS1 S2 hS2
    ext x
    simp only [MinkowskiSumZ, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x1, hx1, x2, hx2, rfl⟩
      refine ⟨EmbedZR x1, embed_mem_closure hx1, EmbedZR x2, embed_mem_closure hx2, ?_⟩
      funext v; simp [EmbedZR]
    · rintro ⟨a, haS, b, hbS, hab⟩
      set T := (fun y => x - y) '' S2 with hT
      have hTF : T ∈ F := (hF S2 hS2).2 x
      by_contra hno
      have hdisj : S1 ∩ T = ∅ := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
        rintro hy ⟨z, hz, rfl⟩
        exact hno ⟨x - z, hy, z, hz, by abel⟩
      have hcl := ha S1 hS1 T hTF hdisj
      have haT : a ∈ ConvexClosureSet T := by
        rw [hT, closure_refl]
        refine ⟨b, hbS, ?_⟩
        rw [reflMap_apply, ← hab]; funext v; simp
      have : a ∈ ConvexClosureSet S1 ∩ ConvexClosureSet T := ⟨haS, haT⟩
      rw [hcl] at this
      exact this
  · intro hb S1 hS1 S2 hS2 hdisj
    by_contra hne
    obtain ⟨w, hw1, hw2⟩ := Set.nonempty_iff_ne_empty.mpr hne
    set T := (fun y => (0 : V → ℤ) - y) '' S2 with hT
    have hTF : T ∈ F := (hF S2 hS2).2 0
    have h0 : (0 : V → ℤ) ∈ MinkowskiSumZ S1 T := by
      rw [hb S1 hS1 T hTF]
      simp only [Set.mem_setOf_eq]
      refine ⟨w, hw1, reflMap (EmbedZR 0) w, ?_, ?_⟩
      · rw [hT, closure_refl]; exact ⟨w, hw2, rfl⟩
      · rw [reflMap_apply]; funext v; simp [EmbedZR]
    obtain ⟨a, ha, t, ⟨z, hz, rfl⟩, hsum⟩ := h0
    have haz : a = z := by
      funext v
      have := congrFun hsum v
      simp at this
      linarith
    have : a ∈ S1 ∩ S2 := ⟨ha, haz ▸ hz⟩
    rw [hdisj] at this
    exact this

#print axioms solution
