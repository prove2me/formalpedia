-- Prove2me | solution 1 for CirclePackingConstants.eight_hull_diam_Xb
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-06T08:49:58.49193+00:00
-- url     : https://prove2.me/submissions/c5359c1a-dcfc-4ac7-8ae9-3230cadc2cc1

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants



theorem convexOn_sqDist (q : Point) : ConvexOn ℝ Set.univ (fun p : Point => sqDist p q) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [sqDist, smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  have h : b = 1 - a := by linarith
  subst h
  nlinarith [mul_nonneg ha hb, sq_nonneg (x.1 - y.1), sq_nonneg (x.2 - y.2)]

theorem hull_close (V : Set Point) (t : ℝ) (hV : ∀ a ∈ V, ∀ b ∈ V, sqDist a b ≤ t) :
    ∀ p ∈ convexHull ℝ V, ∀ q ∈ convexHull ℝ V, sqDist p q ≤ t := by
  intro p hp q hq
  have step1 : ∀ y ∈ V, ∀ p ∈ convexHull ℝ V, sqDist p y ≤ t := by
    intro y hy p hp
    obtain ⟨z, hz, hz'⟩ := (convexOn_sqDist y).exists_ge_of_mem_convexHull (Set.subset_univ V) hp
    exact hz'.trans (hV z hz y hy)
  have hc : ConvexOn ℝ Set.univ (fun q : Point => sqDist p q) := by
    have := convexOn_sqDist p
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have h := this.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    have sym : ∀ x y : Point, sqDist x y = sqDist y x := fun x y => by simp [sqDist]; ring
    rw [sym p (a • x + b • y)] at *
    simp only [sym p x, sym p y] at *
    simpa [sym] using h
  obtain ⟨z, hz, hz'⟩ := hc.exists_ge_of_mem_convexHull (Set.subset_univ V) hq
  exact hz'.trans (by have := step1 z hz p hp; simpa [sqDist] using this)


end CirclePackingConstants

open CirclePackingConstants in
set_option maxHeartbeats 4000000 in
theorem solution :
    ∀ p ∈ convexHull ℝ ({(((-1:ℝ) + ((1:ℝ)/2) * Real.sqrt 3), (((-1:ℝ)/2) + ((1:ℝ)/2) * Real.sqrt 3)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3)), (((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3), ((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * Real.sqrt 3), ((1:ℝ)/2)), (((-1:ℝ) + ((1:ℝ)/2) * Real.sqrt 3), ((1:ℝ)/2))} : Set Point), ∀ q ∈ convexHull ℝ ({(((-1:ℝ) + ((1:ℝ)/2) * Real.sqrt 3), (((-1:ℝ)/2) + ((1:ℝ)/2) * Real.sqrt 3)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3)), (((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3), ((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * Real.sqrt 3), ((1:ℝ)/2)), (((-1:ℝ) + ((1:ℝ)/2) * Real.sqrt 3), ((1:ℝ)/2))} : Set Point),
      sqDist p q ≤ 2 - Real.sqrt 3 := by
  have hr : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hr1 : (1.73:ℝ) < Real.sqrt 3 := by nlinarith [Real.sqrt_nonneg 3]
  have hr2 : Real.sqrt 3 < (1.74:ℝ) := by nlinarith [Real.sqrt_nonneg 3]
  intro p hp q hq
  refine hull_close ({(((-1:ℝ) + ((1:ℝ)/2) * Real.sqrt 3), (((-1:ℝ)/2) + ((1:ℝ)/2) * Real.sqrt 3)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3)), (((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3), ((1:ℝ) + ((-1:ℝ)/2) * Real.sqrt 3)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * Real.sqrt 3), ((1:ℝ)/2)), (((-1:ℝ) + ((1:ℝ)/2) * Real.sqrt 3), ((1:ℝ)/2))} : Set Point) _ ?_ p hp q hq
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl
  all_goals (rcases hb with rfl | rfl | rfl | rfl | rfl)
  all_goals (dsimp only [sqDist]; nlinarith [hr, hr1, hr2])
