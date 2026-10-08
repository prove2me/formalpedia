-- Prove2me | solution 1 for CirclePackingConstants.eight_chase_I
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-06T10:19:33.435124+00:00
-- url     : https://prove2.me/submissions/ea730f1e-f487-400b-b8b2-10becdb30862

import Definitions.Def_CirclePackingConstants
import Definitions.Def_CirclePackingConstants_Eight
import Definitions.Def_CirclePackingConstants_EightQuad
import Theorems.Thm_CirclePackingConstants_eight_hull_diam_Xa
import Theorems.Thm_CirclePackingConstants_eight_hull_diam_Xb
import Theorems.Thm_CirclePackingConstants_eight_hull_diam_Xc
import Theorems.Thm_CirclePackingConstants_eight_hull_diam_rect

noncomputable section

namespace CirclePackingConstants

/-- orientation determinant -/
def cross3 (a b c : Point) : ℝ := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

theorem cross3_rot (a b c : Point) : cross3 a b c = cross3 b c a := by unfold cross3; ring

theorem cross3_swap23 (a b c : Point) : cross3 a c b = - cross3 a b c := by unfold cross3; ring

theorem tri_mem (a b c p : Point) (hD : 0 < cross3 a b c) (h1 : 0 ≤ cross3 p b c)
    (h2 : 0 ≤ cross3 a p c) (h3 : 0 ≤ cross3 a b p) : p ∈ convexHull ℝ {a, b, c} := by
  have hs : Convex ℝ (convexHull ℝ ({a, b, c} : Set Point)) := convex_convexHull ℝ _
  have key := hs.sum_mem (t := (Finset.univ : Finset (Fin 3)))
    (w := ![cross3 p b c / cross3 a b c, cross3 a p c / cross3 a b c, cross3 a b p / cross3 a b c])
    (z := ![a, b, c])
    (by intro i _; fin_cases i <;> simp <;> positivity)
    (by simp [Fin.sum_univ_succ]; field_simp; unfold cross3; ring)
    (by intro i _; fin_cases i <;> simp <;> apply subset_convexHull <;> simp)
  have hD' : cross3 a b c ≠ 0 := hD.ne'
  have e : (∑ i : Fin 3, ![cross3 p b c / cross3 a b c, cross3 a p c / cross3 a b c,
      cross3 a b p / cross3 a b c] i • ![a, b, c] i) = p := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, add_zero]
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      field_simp
      unfold cross3
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      field_simp
      unfold cross3
      ring
  rw [e] at key
  exact key

theorem hull_mono3 (S : Set Point) (a b c : Point) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    convexHull ℝ ({a, b, c} : Set Point) ⊆ convexHull ℝ S := by
  apply convexHull_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> assumption


theorem mem_Xa (r : ℝ) (hr : r * r = 3) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321) (u v : ℝ) (E0 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), (0:ℝ)) (u, v)) (E1 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), (0:ℝ)) (((1:ℝ)/2), (0:ℝ)) (u, v)) (E2 : 0 ≤ cross3 (((1:ℝ)/2), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ)/2)) (u, v)) (E3 : 0 ≤ cross3 (((1:ℝ)/2), ((1:ℝ)/2)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u, v)) (E4 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (u, v)) (E5 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) :
    ((u, v) : Point) ∈ convexHull ℝ ({(((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), (0:ℝ)), (((1:ℝ)/2), (0:ℝ)), (((1:ℝ)/2), ((1:ℝ)/2)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)), (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r))} : Set Point) := by
  rcases le_total (cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ)/2), (0:ℝ)) (u, v)) 0 with hn1 | hp1
  · have hT := tri_mem (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), (0:ℝ)) (((1:ℝ)/2), (0:ℝ)) (u, v)
      (by have e : cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), (0:ℝ)) (((1:ℝ)/2), (0:ℝ)) = (((7:ℝ)/4) + (-1:ℝ) * r) := by dsimp only [cross3]; linear_combination (1/4) * hr
          rw [e]; linarith [hrL, hrU])
      (by rw [cross3_rot]; exact E1)
      (by have e := cross3_swap23 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v) (((1:ℝ)/2), (0:ℝ)); linarith [hn1])
      E0
    exact hull_mono3 ({(((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), (0:ℝ)), (((1:ℝ)/2), (0:ℝ)), (((1:ℝ)/2), ((1:ℝ)/2)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)), (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r))} : Set Point) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), (0:ℝ)) (((1:ℝ)/2), (0:ℝ)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hT
  · rcases le_total (cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ)/2), ((1:ℝ)/2)) (u, v)) 0 with hn2 | hp2
    · have hT := tri_mem (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ)/2), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ)/2)) (u, v)
        (by have e : cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ)/2), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ)/2)) = (((-1:ℝ)/4) + ((1:ℝ)/4) * r) := by dsimp only [cross3]; ring
            rw [e]; linarith [hrL, hrU])
        (by rw [cross3_rot]; exact E2)
        (by have e := cross3_swap23 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v) (((1:ℝ)/2), ((1:ℝ)/2)); linarith [hn2])
        hp1
      exact hull_mono3 ({(((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), (0:ℝ)), (((1:ℝ)/2), (0:ℝ)), (((1:ℝ)/2), ((1:ℝ)/2)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)), (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r))} : Set Point) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ)/2), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ)/2)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) hT
    · rcases le_total (cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u, v)) 0 with hn3 | hp3
      · have hT := tri_mem (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ)/2), ((1:ℝ)/2)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u, v)
          (by have e : cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ)/2), ((1:ℝ)/2)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) = (((-5:ℝ)/4) + ((3:ℝ)/4) * r) := by dsimp only [cross3]; linear_combination (-1/4) * hr
              rw [e]; linarith [hrL, hrU])
          (by rw [cross3_rot]; exact E3)
          (by have e := cross3_swap23 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)); linarith [hn3])
          hp2
        exact hull_mono3 ({(((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), (0:ℝ)), (((1:ℝ)/2), (0:ℝ)), (((1:ℝ)/2), ((1:ℝ)/2)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)), (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r))} : Set Point) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ)/2), ((1:ℝ)/2)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))) hT
      · have hT := tri_mem (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (u, v)
          (by have e : cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) = (((21:ℝ)/4) + (-3:ℝ) * r) := by dsimp only [cross3]; linear_combination (1) * hr
              rw [e]; linarith [hrL, hrU])
          (by rw [cross3_rot]; exact E4)
          (by have h := E5; rwa [cross3_rot] at h)
          hp3
        exact hull_mono3 ({(((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), (0:ℝ)), (((1:ℝ)/2), (0:ℝ)), (((1:ℝ)/2), ((1:ℝ)/2)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)), (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r))} : Set Point) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))) hT

set_option maxHeartbeats 4000000 in
theorem close_Xa (r : ℝ) (hrs : r = Real.sqrt 3) (hr : r * r = 3) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321)
    (u1 v1 u2 v2 : ℝ) (E0 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), (0:ℝ)) (u1, v1)) (E1 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), (0:ℝ)) (((1:ℝ)/2), (0:ℝ)) (u1, v1)) (E2 : 0 ≤ cross3 (((1:ℝ)/2), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ)/2)) (u1, v1)) (E3 : 0 ≤ cross3 (((1:ℝ)/2), ((1:ℝ)/2)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u1, v1)) (E4 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (u1, v1)) (E5 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1))
    (F0 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), (0:ℝ)) (u2, v2)) (F1 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), (0:ℝ)) (((1:ℝ)/2), (0:ℝ)) (u2, v2)) (F2 : 0 ≤ cross3 (((1:ℝ)/2), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ)/2)) (u2, v2)) (F3 : 0 ≤ cross3 (((1:ℝ)/2), ((1:ℝ)/2)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u2, v2)) (F4 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (u2, v2)) (F5 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u2, v2)) :
    sqDist (u1, v1) (u2, v2) ≤ 2 - r := by
  subst hrs
  exact eight_hull_diam_Xa _ (mem_Xa _ hr hrL hrU u1 v1 E0 E1 E2 E3 E4 E5) _ (mem_Xa _ hr hrL hrU u2 v2 F0 F1 F2 F3 F4 F5)

theorem mem_Xb (r : ℝ) (hr : r * r = 3) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321) (u v : ℝ) (E0 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) (E1 : 0 ≤ cross3 ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) (E2 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u, v)) (E3 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u, v)) (E4 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (u, v)) :
    ((u, v) : Point) ∈ convexHull ℝ ({(((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2))} : Set Point) := by
  rcases le_total (cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) 0 with hn1 | hp1
  · have hT := tri_mem (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)
      (by have e : cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) = ((-3:ℝ) + ((7:ℝ)/4) * r) := by dsimp only [cross3]; linear_combination (-1/2) * hr
          rw [e]; linarith [hrL, hrU])
      (by rw [cross3_rot]; exact E1)
      (by have e := cross3_swap23 (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (u, v) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)); linarith [hn1])
      E0
    exact hull_mono3 ({(((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2))} : Set Point) (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hT
  · rcases le_total (cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u, v)) 0 with hn2 | hp2
    · have hT := tri_mem (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u, v)
        (by have e : cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) = (((11:ℝ)/4) + ((-3:ℝ)/2) * r) := by dsimp only [cross3]; linear_combination (1/2) * hr
            rw [e]; linarith [hrL, hrU])
        (by rw [cross3_rot]; exact E2)
        (by have e := cross3_swap23 (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (u, v) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)); linarith [hn2])
        hp1
      exact hull_mono3 ({(((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2))} : Set Point) (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) hT
    · have hT := tri_mem (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u, v)
        (by have e : cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) = (((1:ℝ)/2) + ((-1:ℝ)/4) * r) := by dsimp only [cross3]; ring
            rw [e]; linarith [hrL, hrU])
        (by rw [cross3_rot]; exact E3)
        (by have h := E4; rwa [cross3_rot] at h)
        hp2
      exact hull_mono3 ({(((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2))} : Set Point) (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))) hT

set_option maxHeartbeats 4000000 in
theorem close_Xb (r : ℝ) (hrs : r = Real.sqrt 3) (hr : r * r = 3) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321)
    (u1 v1 u2 v2 : ℝ) (E0 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) (E1 : 0 ≤ cross3 ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) (E2 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u1, v1)) (E3 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u1, v1)) (E4 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (u1, v1))
    (F0 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u2, v2)) (F1 : 0 ≤ cross3 ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u2, v2)) (F2 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u2, v2)) (F3 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u2, v2)) (F4 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (u2, v2)) :
    sqDist (u1, v1) (u2, v2) ≤ 2 - r := by
  subst hrs
  exact eight_hull_diam_Xb _ (mem_Xb _ hr hrL hrU u1 v1 E0 E1 E2 E3 E4) _ (mem_Xb _ hr hrL hrU u2 v2 F0 F1 F2 F3 F4)

theorem mem_Xc (r : ℝ) (hr : r * r = 3) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321) (u v : ℝ) (E0 : 0 ≤ cross3 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) (E1 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (u, v)) (E2 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u, v)) (E3 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ)/2), ((1:ℝ)/2)) (u, v)) (E4 : 0 ≤ cross3 (((-1:ℝ)/2), ((1:ℝ)/2)) (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) :
    ((u, v) : Point) ∈ convexHull ℝ ({(((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)), (((-1:ℝ)/2), ((1:ℝ)/2))} : Set Point) := by
  rcases le_total (cross3 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (u, v)) 0 with hn1 | hp1
  · have hT := tri_mem (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (u, v)
      (by have e : cross3 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) = (((9:ℝ)/8) + ((-5:ℝ)/8) * r) := by dsimp only [cross3]; linear_combination (1/4) * hr
          rw [e]; linarith [hrL, hrU])
      (by rw [cross3_rot]; exact E1)
      (by have e := cross3_swap23 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)); linarith [hn1])
      E0
    exact hull_mono3 ({(((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)), (((-1:ℝ)/2), ((1:ℝ)/2))} : Set Point) (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hT
  · rcases le_total (cross3 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u, v)) 0 with hn2 | hp2
    · have hT := tri_mem (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u, v)
        (by have e : cross3 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) = (((-3:ℝ)/4) + ((1:ℝ)/2) * r) := by dsimp only [cross3]; linear_combination (-1/8) * hr
            rw [e]; linarith [hrL, hrU])
        (by rw [cross3_rot]; exact E2)
        (by have e := cross3_swap23 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)); linarith [hn2])
        hp1
      exact hull_mono3 ({(((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)), (((-1:ℝ)/2), ((1:ℝ)/2))} : Set Point) (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) hT
    · have hT := tri_mem (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ)/2), ((1:ℝ)/2)) (u, v)
        (by have e : cross3 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ)/2), ((1:ℝ)/2)) = ((1:ℝ) + ((-1:ℝ)/2) * r) := by dsimp only [cross3]; linear_combination (1/4) * hr
            rw [e]; linarith [hrL, hrU])
        (by rw [cross3_rot]; exact E3)
        (by have h := E4; rwa [cross3_rot] at h)
        hp2
      exact hull_mono3 ({(((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)), (((-1:ℝ)/2), ((1:ℝ)/2))} : Set Point) (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ)/2), ((1:ℝ)/2)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))) hT

set_option maxHeartbeats 4000000 in
theorem close_Xc (r : ℝ) (hrs : r = Real.sqrt 3) (hr : r * r = 3) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321)
    (u1 v1 u2 v2 : ℝ) (E0 : 0 ≤ cross3 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) (E1 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (u1, v1)) (E2 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u1, v1)) (E3 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ)/2), ((1:ℝ)/2)) (u1, v1)) (E4 : 0 ≤ cross3 (((-1:ℝ)/2), ((1:ℝ)/2)) (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1))
    (F0 : 0 ≤ cross3 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u2, v2)) (F1 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (u2, v2)) (F2 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (u2, v2)) (F3 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((-1:ℝ)/2), ((1:ℝ)/2)) (u2, v2)) (F4 : 0 ≤ cross3 (((-1:ℝ)/2), ((1:ℝ)/2)) (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u2, v2)) :
    sqDist (u1, v1) (u2, v2) ≤ 2 - r := by
  subst hrs
  exact eight_hull_diam_Xc _ (mem_Xc _ hr hrL hrU u1 v1 E0 E1 E2 E3 E4) _ (mem_Xc _ hr hrL hrU u2 v2 F0 F1 F2 F3 F4)

theorem mem_rect (r : ℝ) (hr : r * r = 3) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321) (u v : ℝ) (E0 : 0 ≤ cross3 ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), (0:ℝ)) (u, v)) (E1 : 0 ≤ cross3 (((1:ℝ)/2), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) (E2 : 0 ≤ cross3 (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) (E3 : 0 ≤ cross3 ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), (0:ℝ)) (u, v)) :
    ((u, v) : Point) ∈ convexHull ℝ ({((0:ℝ), (0:ℝ)), (((1:ℝ)/2), (0:ℝ)), (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r))} : Set Point) := by
  rcases le_total (cross3 ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) 0 with hn1 | hp1
  · have hT := tri_mem ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)
      (by have e : cross3 ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) = (((1:ℝ)/2) + ((-1:ℝ)/4) * r) := by dsimp only [cross3]; ring
          rw [e]; linarith [hrL, hrU])
      (by rw [cross3_rot]; exact E1)
      (by have e := cross3_swap23 ((0:ℝ), (0:ℝ)) (u, v) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)); linarith [hn1])
      E0
    exact hull_mono3 ({((0:ℝ), (0:ℝ)), (((1:ℝ)/2), (0:ℝ)), (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r))} : Set Point) ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hT
  · have hT := tri_mem ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)
      (by have e : cross3 ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) = (((1:ℝ)/2) + ((-1:ℝ)/4) * r) := by dsimp only [cross3]; ring
          rw [e]; linarith [hrL, hrU])
      (by rw [cross3_rot]; exact E2)
      (by have h := E3; rwa [cross3_rot] at h)
      hp1
    exact hull_mono3 ({((0:ℝ), (0:ℝ)), (((1:ℝ)/2), (0:ℝ)), (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r))} : Set Point) ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) hT

set_option maxHeartbeats 4000000 in
theorem close_rect (r : ℝ) (hrs : r = Real.sqrt 3) (hr : r * r = 3) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321)
    (u1 v1 u2 v2 : ℝ) (E0 : 0 ≤ cross3 ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), (0:ℝ)) (u1, v1)) (E1 : 0 ≤ cross3 (((1:ℝ)/2), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) (E2 : 0 ≤ cross3 (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) (E3 : 0 ≤ cross3 ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), (0:ℝ)) (u1, v1))
    (F0 : 0 ≤ cross3 ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), (0:ℝ)) (u2, v2)) (F1 : 0 ≤ cross3 (((1:ℝ)/2), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u2, v2)) (F2 : 0 ≤ cross3 (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u2, v2)) (F3 : 0 ≤ cross3 ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), (0:ℝ)) (u2, v2)) :
    sqDist (u1, v1) (u2, v2) ≤ 2 - r := by
  subst hrs
  exact eight_hull_diam_rect _ (mem_rect _ hr hrL hrU u1 v1 E0 E1 E2 E3) _ (mem_rect _ hr hrL hrU u2 v2 F0 F1 F2 F3)

set_option maxHeartbeats 40000000 in
theorem chaseI_vars (r : ℝ) (hrs : r = Real.sqrt 3) (hr : r * r = 3) (hr0 : 0 ≤ r) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321)
    (u0 v0 u1 v1 u2 v2 u7 v7 : ℝ)
    (hc0_0 : 0 ≤ (1:ℝ) * u0 + (0:ℝ) * v0 + ((-1:ℝ) + ((1:ℝ)/2) * r))
    (hc0_1 : 0 ≤ (-1:ℝ) * u0 + (0:ℝ) * v0 + ((1:ℝ)/2))
    (hc0_2 : 0 ≤ (0:ℝ) * u0 + (1:ℝ) * v0 + ((-1:ℝ) + ((1:ℝ)/2) * r))
    (hc0_3 : 0 ≤ (0:ℝ) * u0 + (-1:ℝ) * v0 + ((1:ℝ)/2))
    (hc1_0 : 0 ≤ (1:ℝ) * u1 + (0:ℝ) * v1 + ((1:ℝ) + ((-1:ℝ)/2) * r))
    (hc1_1 : 0 ≤ (-1:ℝ) * u1 + (0:ℝ) * v1 + ((1:ℝ) + ((-1:ℝ)/2) * r))
    (hc1_2 : 0 ≤ (-1:ℝ) * u1 + (1:ℝ) * v1 + (0:ℝ))
    (hc1_3 : 0 ≤ (1:ℝ) * u1 + (1:ℝ) * v1 + (0:ℝ))
    (hc1_4 : 0 ≤ (0:ℝ) * u1 + (-1:ℝ) * v1 + ((1:ℝ)/2))
    (hc2_0 : 0 ≤ (1:ℝ) * u2 + (0:ℝ) * v2 + ((1:ℝ)/2))
    (hc2_1 : 0 ≤ (-1:ℝ) * u2 + (0:ℝ) * v2 + ((-1:ℝ) + ((1:ℝ)/2) * r))
    (hc2_2 : 0 ≤ (0:ℝ) * u2 + (1:ℝ) * v2 + ((-1:ℝ) + ((1:ℝ)/2) * r))
    (hc2_3 : 0 ≤ (0:ℝ) * u2 + (-1:ℝ) * v2 + ((1:ℝ)/2))
    (hc7_0 : 0 ≤ (0:ℝ) * u7 + (1:ℝ) * v7 + ((1:ℝ) + ((-1:ℝ)/2) * r))
    (hc7_1 : 0 ≤ (0:ℝ) * u7 + (-1:ℝ) * v7 + ((1:ℝ) + ((-1:ℝ)/2) * r))
    (hc7_2 : 0 ≤ (1:ℝ) * u7 + (-1:ℝ) * v7 + (0:ℝ))
    (hc7_3 : 0 ≤ (1:ℝ) * u7 + (1:ℝ) * v7 + (0:ℝ))
    (hc7_4 : 0 ≤ (-1:ℝ) * u7 + (0:ℝ) * v7 + ((1:ℝ)/2))
    (hT_0 : 0 ≤ (0:ℝ) * u7 + (1:ℝ) * v7 + (0:ℝ))
    (hT_1 : 0 ≤ (1:ℝ) * u7 + (1:ℝ) * v7 + (((1:ℝ)/2) + ((-1:ℝ)/2) * r))
    (hd_0_1 : 2 - r < sqDist (u0, v0) (u1, v1))
    (hd_0_7 : 2 - r < sqDist (u0, v0) (u7, v7))
    (hd_1_2 : 2 - r < sqDist (u1, v1) (u2, v2))
    (hd_1_7 : 2 - r < sqDist (u1, v1) (u7, v7))
    : 0 ≤ (-1:ℝ) * u1 + (0:ℝ) * v1 + (0:ℝ) ∧ 0 ≤ (1:ℝ) * u1 + (1:ℝ) * v1 + (0:ℝ) ∧ 0 ≤ ((-1:ℝ) * r) * u1 + (-1:ℝ) * v1 + ((1:ℝ) + ((-1:ℝ)/2) * r) ∧ 0 ≤ ((1:ℝ) * r) * u1 + (-1:ℝ) * v1 + (((-1:ℝ)/2) + ((1:ℝ)/2) * r) := by
  have hru0 : r * r * u0 = 3 * u0 := by rw [hr]
  have hrv0 : r * r * v0 = 3 * v0 := by rw [hr]
  have hru1 : r * r * u1 = 3 * u1 := by rw [hr]
  have hrv1 : r * r * v1 = 3 * v1 := by rw [hr]
  have hru2 : r * r * u2 = 3 * u2 := by rw [hr]
  have hrv2 : r * r * v2 = 3 * v2 := by rw [hr]
  have hru7 : r * r * u7 = 3 * u7 := by rw [hr]
  have hrv7 : r * r * v7 = 3 * v7 := by rw [hr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hneg0
    push Not at hneg0
    have hfn0 : 0 < (1:ℝ) * u1 + (0:ℝ) * v1 + (0:ℝ) := by linarith only [hneg0]
    rcases lt_or_ge (cross3 ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (u0, v0)) 0 with hN0 | hP0
    · have fN0 : 0 < ((-1:ℝ) + ((1:ℝ)/2) * r) * u0 + (((-3:ℝ)/2) + (1:ℝ) * r) * v0 + (((-1:ℝ)/2) + ((1:ℝ)/4) * r) := by dsimp only [cross3] at hN0; linarith only [hN0, hr, hru0, hrv0]
      rcases lt_or_ge (cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) 0 with hN1 | hP1
      · have fN1 : 0 < (((3:ℝ)/2) + (-1:ℝ) * r) * u1 + ((-1:ℝ) + ((1:ℝ)/2) * r) * v1 + (((7:ℝ)/4) + (-1:ℝ) * r) := by dsimp only [cross3] at hN1; linarith only [hN1, hr, hru1, hrv1]
        rcases lt_or_ge (cross3 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) 0 with hN2 | hP2
        · have fN2 : 0 < (0:ℝ) * u1 + (((1:ℝ)/2) + ((-1:ℝ)/2) * r) * v1 + (((-5:ℝ)/4) + ((3:ℝ)/4) * r) := by dsimp only [cross3] at hN2; linarith only [hN2, hr, hru1, hrv1]
          exact absurd (close_rect r hrs hr hrL hrU u1 v1 u7 v7 (by dsimp only [cross3]; linear_combination ((1:ℝ)/4) * hc1_2 + ((1:ℝ)/4) * hc1_3) (by dsimp only [cross3]; linear_combination ((3769136859:ℝ)/28134340000) * hc1_1 + ((578921:ℝ)/2813434) * (mul_nonneg (sub_nonneg.2 hrU) hc1_1) + ((151500:ℝ)/1406717) * (mul_nonneg (sub_nonneg.2 hrL) hc1_3) + ((33:ℝ)/11253736) * (mul_nonneg hr0 hc1_4) + ((162375:ℝ)/2813434) * (mul_nonneg (sub_nonneg.2 hrL) fN1.le) + ((1103651:ℝ)/22507472) * (zero_le_one : (0:ℝ) ≤ 1) + ((-162375:ℝ)/2813434) * hru1 + ((162375:ℝ)/5626868) * hrv1 + ((254171:ℝ)/5626868) * hr) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * fN2.le + ((1:ℝ)/2) * (mul_nonneg hr0 fN2.le) + ((-1:ℝ)/4) * hrv1 + ((3:ℝ)/8) * hr) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hfn0.le + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hfn0.le)) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hT_0) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc7_4 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc7_4)) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc7_1) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/40000) * hc7_2 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hc7_2) + ((2679:ℝ)/40000) * hc7_3 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hc7_3))) (not_le.2 hd_1_7)
        · have fP2 : 0 ≤ (0:ℝ) * u1 + (((-1:ℝ)/2) + ((1:ℝ)/2) * r) * v1 + (((5:ℝ)/4) + ((-3:ℝ)/4) * r) := by dsimp only [cross3] at hP2; linarith only [hP2, hr, hru1, hrv1]
          exact absurd (by linarith only [hc1_0, mul_nonneg hr0 hc1_0, mul_nonneg (sub_nonneg.2 hrL) hc1_0, mul_nonneg (sub_nonneg.2 hrU) hc1_0, hc1_1, mul_nonneg hr0 hc1_1, mul_nonneg (sub_nonneg.2 hrL) hc1_1, mul_nonneg (sub_nonneg.2 hrU) hc1_1, hc1_2, mul_nonneg hr0 hc1_2, mul_nonneg (sub_nonneg.2 hrL) hc1_2, mul_nonneg (sub_nonneg.2 hrU) hc1_2, hc1_3, mul_nonneg hr0 hc1_3, mul_nonneg (sub_nonneg.2 hrL) hc1_3, mul_nonneg (sub_nonneg.2 hrU) hc1_3, hc1_4, mul_nonneg hr0 hc1_4, mul_nonneg (sub_nonneg.2 hrL) hc1_4, mul_nonneg (sub_nonneg.2 hrU) hc1_4, hfn0.le, mul_nonneg hr0 hfn0.le, mul_nonneg (sub_nonneg.2 hrL) hfn0.le, mul_nonneg (sub_nonneg.2 hrU) hfn0.le, hfn0, fN1.le, mul_nonneg hr0 fN1.le, mul_nonneg (sub_nonneg.2 hrL) fN1.le, mul_nonneg (sub_nonneg.2 hrU) fN1.le, fN1, fP2, mul_nonneg hr0 fP2, mul_nonneg (sub_nonneg.2 hrL) fP2, mul_nonneg (sub_nonneg.2 hrU) fP2, hr, hr0, hrL, hrU, hru1, hrv1]) (lt_irrefl (0:ℝ))
      · have fP1 : 0 ≤ (((-3:ℝ)/2) + (1:ℝ) * r) * u1 + ((1:ℝ) + ((-1:ℝ)/2) * r) * v1 + (((-7:ℝ)/4) + (1:ℝ) * r) := by dsimp only [cross3] at hP1; linarith only [hP1, hr, hru1, hrv1]
        rcases lt_or_ge (cross3 ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) 0 with hN3 | hP3
        · have fN3 : 0 < (0:ℝ) * u1 + ((-1:ℝ) + ((1:ℝ)/2) * r) * v1 + (((7:ℝ)/4) + (-1:ℝ) * r) := by dsimp only [cross3] at hN3; linarith only [hN3, hr, hru1, hrv1]
          rcases lt_or_ge (cross3 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) 0 with hN4 | hP4
          · have fN4 : 0 < (0:ℝ) * u1 + (((1:ℝ)/2) + ((-1:ℝ)/2) * r) * v1 + (((-5:ℝ)/4) + ((3:ℝ)/4) * r) := by dsimp only [cross3] at hN4; linarith only [hN4, hr, hru1, hrv1]
            exact absurd (close_rect r hrs hr hrL hrU u1 v1 u7 v7 (by dsimp only [cross3]; linear_combination ((1:ℝ)/4) * hc1_2 + ((1:ℝ)/4) * hc1_3) (by dsimp only [cross3]; linear_combination ((646402959:ℝ)/4824940000) * hc1_1 + ((47321:ℝ)/482494) * (mul_nonneg (sub_nonneg.2 hrU) hc1_1) + ((30000:ℝ)/241247) * (mul_nonneg (sub_nonneg.2 hrU) fP1) + ((30000:ℝ)/241247) * (mul_nonneg (sub_nonneg.2 hrU) fN3.le) + ((47321:ℝ)/964988) * (zero_le_one : (0:ℝ) ≤ 1) + ((-30000:ℝ)/241247) * hru1 + ((47321:ℝ)/964988) * hr) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * fN4.le + ((1:ℝ)/2) * (mul_nonneg hr0 fN4.le) + ((-1:ℝ)/4) * hrv1 + ((3:ℝ)/8) * hr) (by dsimp only [cross3]; linear_combination ((433:ℝ)/5598) * (mul_nonneg hr0 hfn0.le) + ((500:ℝ)/2799) * (mul_nonneg (sub_nonneg.2 hrL) fP1) + ((500:ℝ)/2799) * (mul_nonneg (sub_nonneg.2 hrL) fN3.le) + ((500:ℝ)/2799) * hru1) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hT_0) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc7_4 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc7_4)) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc7_1) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/40000) * hc7_2 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hc7_2) + ((2679:ℝ)/40000) * hc7_3 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hc7_3))) (not_le.2 hd_1_7)
          · have fP4 : 0 ≤ (0:ℝ) * u1 + (((-1:ℝ)/2) + ((1:ℝ)/2) * r) * v1 + (((5:ℝ)/4) + ((-3:ℝ)/4) * r) := by dsimp only [cross3] at hP4; linarith only [hP4, hr, hru1, hrv1]
            exact absurd (by linarith only [hc1_0, mul_nonneg hr0 hc1_0, mul_nonneg (sub_nonneg.2 hrL) hc1_0, mul_nonneg (sub_nonneg.2 hrU) hc1_0, hc1_1, mul_nonneg hr0 hc1_1, mul_nonneg (sub_nonneg.2 hrL) hc1_1, mul_nonneg (sub_nonneg.2 hrU) hc1_1, hc1_2, mul_nonneg hr0 hc1_2, mul_nonneg (sub_nonneg.2 hrL) hc1_2, mul_nonneg (sub_nonneg.2 hrU) hc1_2, hc1_3, mul_nonneg hr0 hc1_3, mul_nonneg (sub_nonneg.2 hrL) hc1_3, mul_nonneg (sub_nonneg.2 hrU) hc1_3, hc1_4, mul_nonneg hr0 hc1_4, mul_nonneg (sub_nonneg.2 hrL) hc1_4, mul_nonneg (sub_nonneg.2 hrU) hc1_4, hfn0.le, mul_nonneg hr0 hfn0.le, mul_nonneg (sub_nonneg.2 hrL) hfn0.le, mul_nonneg (sub_nonneg.2 hrU) hfn0.le, hfn0, fP1, mul_nonneg hr0 fP1, mul_nonneg (sub_nonneg.2 hrL) fP1, mul_nonneg (sub_nonneg.2 hrU) fP1, fN3.le, mul_nonneg hr0 fN3.le, mul_nonneg (sub_nonneg.2 hrL) fN3.le, mul_nonneg (sub_nonneg.2 hrU) fN3.le, fN3, fP4, mul_nonneg hr0 fP4, mul_nonneg (sub_nonneg.2 hrL) fP4, mul_nonneg (sub_nonneg.2 hrU) fP4, hr, hr0, hrL, hrU, hru1, hrv1]) (lt_irrefl (0:ℝ))
        · have fP3 : 0 ≤ (0:ℝ) * u1 + ((1:ℝ) + ((-1:ℝ)/2) * r) * v1 + (((-7:ℝ)/4) + (1:ℝ) * r) := by dsimp only [cross3] at hP3; linarith only [hP3, hr, hru1, hrv1]
          exact absurd (close_Xb r hrs hr hrL hrU u0 v0 u1 v1 (by dsimp only [cross3]; linear_combination ((366580664:ℝ)/2735765205) * (mul_nonneg hr0 hc0_0) + ((400531000:ℝ)/547153041) * (mul_nonneg (sub_nonneg.2 hrU) hc0_1) + ((7328445545551:ℝ)/54715304100000) * hc0_2 + ((4005463369:ℝ)/5471530410) * (mul_nonneg (sub_nonneg.2 hrU) hc0_2) + ((39284000:ℝ)/547153041) * (mul_nonneg (sub_nonneg.2 hrU) fN0.le) + ((340065713:ℝ)/10943060820) * (zero_le_one : (0:ℝ) ≤ 1) + ((-19642000:ℝ)/547153041) * hru0 + ((-39284000:ℝ)/547153041) * hrv0 + ((-10778777:ℝ)/160927365) * hr) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc0_2 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc0_2)) (by dsimp only [cross3]; linear_combination ((8037:ℝ)/20000) * hc0_3 + ((3:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc0_3) + (1:ℝ) * fN0.le + (1:ℝ) * (mul_nonneg hr0 fN0.le) + ((1:ℝ)/2) * hru0 + (1:ℝ) * hrv0) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc0_3) (by dsimp only [cross3]; linear_combination ((114538763:ℝ)/1480605396) * (mul_nonneg hr0 hc0_0) + ((107764250:ℝ)/370151349) * (mul_nonneg (sub_nonneg.2 hrL) hc0_1) + ((122339625:ℝ)/246767566) * (mul_nonneg (sub_nonneg.2 hrL) hc0_2) + ((11539:ℝ)/740302698) * (mul_nonneg hr0 hc0_3) + ((131125:ℝ)/854853) * (mul_nonneg (sub_nonneg.2 hrL) fN0.le) + ((245401:ℝ)/6838824) * (zero_le_one : (0:ℝ) ≤ 1) + ((131125:ℝ)/1709706) * hru0 + ((131125:ℝ)/854853) * hrv0 + ((512305:ℝ)/6838824) * hr) (by dsimp only [cross3]; linear_combination (1:ℝ) * fP1 + ((1:ℝ)/4) * hr) (by dsimp only [cross3]; linear_combination (1:ℝ) * fP3 + ((1:ℝ)/4) * hr) (by dsimp only [cross3]; linear_combination ((125:ℝ)/1616) * (mul_nonneg hr0 hc1_1) + ((93739:ℝ)/699728) * (mul_nonneg hr0 hc1_2) + ((125:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hc1_2) + ((125:ℝ)/404) * (mul_nonneg (sub_nonneg.2 hrL) fP3) + ((-125:ℝ)/808) * hrv1 + ((67:ℝ)/3232) * hr) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc1_4) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc1_0 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc1_0))) (not_le.2 hd_0_1)
    · have fP0 : 0 ≤ ((1:ℝ) + ((-1:ℝ)/2) * r) * u0 + (((3:ℝ)/2) + (-1:ℝ) * r) * v0 + (((1:ℝ)/2) + ((-1:ℝ)/4) * r) := by dsimp only [cross3] at hP0; linarith only [hP0, hr, hru0, hrv0]
      exact absurd (close_Xa r hrs hr hrL hrU u0 v0 u7 v7 (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc0_0 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc0_0) + ((58:ℝ)/433) * (mul_nonneg hr0 hc0_2) + ((375:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hc0_2)) (by dsimp only [cross3]; linear_combination ((17041:ℝ)/2735765205) * (mul_nonneg hr0 hc0_0) + ((129284000:ℝ)/547153041) * (mul_nonneg (sub_nonneg.2 hrU) hc0_1) + ((7330295652839:ℝ)/54715304100000) * hc0_2 + ((496437041:ℝ)/5471530410) * (mul_nonneg (sub_nonneg.2 hrU) hc0_2) + ((69284000:ℝ)/547153041) * (mul_nonneg (sub_nonneg.2 hrU) fP0) + ((196368877:ℝ)/10943060820) * (zero_le_one : (0:ℝ) ≤ 1) + ((34642000:ℝ)/547153041) * hru0 + ((69284000:ℝ)/547153041) * hrv0 + ((-8822527:ℝ)/643709460) * hr) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc0_1) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc0_3 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc0_3)) (by dsimp only [cross3]; linear_combination (1:ℝ) * fP0 + ((-1:ℝ)/4) * hr) (by dsimp only [cross3]; linear_combination ((58:ℝ)/433) * (mul_nonneg hr0 hc0_0) + ((375:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hc0_0)) (by dsimp only [cross3]; linear_combination ((49:ℝ)/866) * (mul_nonneg hr0 hT_0) + ((625:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hT_0) + ((2679:ℝ)/20000) * hT_1 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hT_1)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hT_0 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hT_0)) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc7_4) (by dsimp only [cross3]; linear_combination ((125:ℝ)/622) * (mul_nonneg (sub_nonneg.2 hrL) hc7_0) + ((416647:ℝ)/3110000) * hc7_1 + ((93:ℝ)/311) * (mul_nonneg (sub_nonneg.2 hrU) hc7_1) + ((61:ℝ)/1244) * (zero_le_one : (0:ℝ) ≤ 1) + ((61:ℝ)/1244) * hr) (by dsimp only [cross3]; linear_combination ((106235000:ℝ)/646437041) * (mul_nonneg (sub_nonneg.2 hrU) hc7_0) + ((1963:ℝ)/34642) * (mul_nonneg hr0 hc7_1) + ((43290611997:ℝ)/559814477506) * (mul_nonneg hr0 hc7_2) + ((1004625:ℝ)/16159993) * (mul_nonneg (sub_nonneg.2 hrL) hc7_2) + ((413395000:ℝ)/646437041) * (mul_nonneg (sub_nonneg.2 hrU) hc7_3) + ((8037:ℝ)/149284) * (zero_le_one : (0:ℝ) ≤ 1) + ((-7321:ℝ)/37321) * hr) (by dsimp only [cross3]; linear_combination ((294630000:ℝ)/819647041) * (mul_nonneg (sub_nonneg.2 hrU) hc7_0) + ((294630000:ℝ)/819647041) * (mul_nonneg (sub_nonneg.2 hrU) hc7_1) + ((2321:ℝ)/34642) * (mul_nonneg hr0 hc7_2) + ((14688418:ℝ)/819647041) * (mul_nonneg hr0 hc7_3) + ((15000:ℝ)/17321) * (mul_nonneg (sub_nonneg.2 hrU) hc7_4) + ((80455205:ℝ)/1639294082) * (mul_nonneg hr0 hT_1) + ((-31247:ℝ)/189284) * hr)) (not_le.2 hd_0_7)
  · by_contra hneg1
    push Not at hneg1
    have hfn1 : 0 < (-1:ℝ) * u1 + (-1:ℝ) * v1 + (0:ℝ) := by linarith only [hneg1]
    exact absurd (by linarith only [hc1_0, mul_nonneg hr0 hc1_0, mul_nonneg (sub_nonneg.2 hrL) hc1_0, mul_nonneg (sub_nonneg.2 hrU) hc1_0, hc1_1, mul_nonneg hr0 hc1_1, mul_nonneg (sub_nonneg.2 hrL) hc1_1, mul_nonneg (sub_nonneg.2 hrU) hc1_1, hc1_2, mul_nonneg hr0 hc1_2, mul_nonneg (sub_nonneg.2 hrL) hc1_2, mul_nonneg (sub_nonneg.2 hrU) hc1_2, hc1_3, mul_nonneg hr0 hc1_3, mul_nonneg (sub_nonneg.2 hrL) hc1_3, mul_nonneg (sub_nonneg.2 hrU) hc1_3, hc1_4, mul_nonneg hr0 hc1_4, mul_nonneg (sub_nonneg.2 hrL) hc1_4, mul_nonneg (sub_nonneg.2 hrU) hc1_4, hfn1.le, mul_nonneg hr0 hfn1.le, mul_nonneg (sub_nonneg.2 hrL) hfn1.le, mul_nonneg (sub_nonneg.2 hrU) hfn1.le, hfn1, hr, hr0, hrL, hrU, hru1, hrv1]) (lt_irrefl (0:ℝ))
  · by_contra hneg2
    push Not at hneg2
    have hfn2 : 0 < ((1:ℝ) * r) * u1 + (1:ℝ) * v1 + ((-1:ℝ) + ((1:ℝ)/2) * r) := by linarith only [hneg2]
    rcases lt_or_ge (cross3 ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (u0, v0)) 0 with hN200 | hP200
    · have fN200 : 0 < ((-1:ℝ) + ((1:ℝ)/2) * r) * u0 + (((-3:ℝ)/2) + (1:ℝ) * r) * v0 + (((-1:ℝ)/2) + ((1:ℝ)/4) * r) := by dsimp only [cross3] at hN200; linarith only [hN200, hr, hru0, hrv0]
      rcases lt_or_ge (cross3 ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) 0 with hN201 | hP201
      · have fN201 : 0 < (0:ℝ) * u1 + ((-1:ℝ) + ((1:ℝ)/2) * r) * v1 + (((7:ℝ)/4) + (-1:ℝ) * r) := by dsimp only [cross3] at hN201; linarith only [hN201, hr, hru1, hrv1]
        rcases lt_or_ge (cross3 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) 0 with hN202 | hP202
        · have fN202 : 0 < (0:ℝ) * u1 + (((1:ℝ)/2) + ((-1:ℝ)/2) * r) * v1 + (((-5:ℝ)/4) + ((3:ℝ)/4) * r) := by dsimp only [cross3] at hN202; linarith only [hN202, hr, hru1, hrv1]
          exact absurd (close_rect r hrs hr hrL hrU u1 v1 u7 v7 (by dsimp only [cross3]; linear_combination ((1:ℝ)/4) * hc1_2 + ((1:ℝ)/4) * hc1_3) (by dsimp only [cross3]; linear_combination ((53869183749:ℝ)/402071480000) * hc1_1 + ((8273331:ℝ)/40207148) * (mul_nonneg (sub_nonneg.2 hrU) hc1_1) + ((2165125:ℝ)/20103574) * (mul_nonneg (sub_nonneg.2 hrL) hc1_3) + ((125:ℝ)/20103574) * (mul_nonneg hr0 hc1_4) + ((1082500:ℝ)/10051787) * (mul_nonneg (sub_nonneg.2 hrU) hfn2.le) + ((3942831:ℝ)/80414296) * (zero_le_one : (0:ℝ) ≤ 1) + ((-1082500:ℝ)/10051787) * hru1 + ((3943331:ℝ)/80414296) * hr) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * fN202.le + ((1:ℝ)/2) * (mul_nonneg hr0 fN202.le) + ((-1:ℝ)/4) * hrv1 + ((3:ℝ)/8) * hr) (by dsimp only [cross3]; linear_combination ((58:ℝ)/1299) * (mul_nonneg hr0 hfn2.le) + ((125:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hfn2.le) + ((1:ℝ)/3) * (mul_nonneg hr0 fN201.le) + ((1:ℝ)/3) * hru1 + ((1:ℝ)/6) * hrv1 + ((-1:ℝ)/6) * hr) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hT_0) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc7_4 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc7_4)) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc7_1) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/40000) * hc7_2 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hc7_2) + ((2679:ℝ)/40000) * hc7_3 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hc7_3))) (not_le.2 hd_1_7)
        · have fP202 : 0 ≤ (0:ℝ) * u1 + (((-1:ℝ)/2) + ((1:ℝ)/2) * r) * v1 + (((5:ℝ)/4) + ((-3:ℝ)/4) * r) := by dsimp only [cross3] at hP202; linarith only [hP202, hr, hru1, hrv1]
          exact absurd (by linarith only [hc1_0, mul_nonneg hr0 hc1_0, mul_nonneg (sub_nonneg.2 hrL) hc1_0, mul_nonneg (sub_nonneg.2 hrU) hc1_0, hc1_1, mul_nonneg hr0 hc1_1, mul_nonneg (sub_nonneg.2 hrL) hc1_1, mul_nonneg (sub_nonneg.2 hrU) hc1_1, hc1_2, mul_nonneg hr0 hc1_2, mul_nonneg (sub_nonneg.2 hrL) hc1_2, mul_nonneg (sub_nonneg.2 hrU) hc1_2, hc1_3, mul_nonneg hr0 hc1_3, mul_nonneg (sub_nonneg.2 hrL) hc1_3, mul_nonneg (sub_nonneg.2 hrU) hc1_3, hc1_4, mul_nonneg hr0 hc1_4, mul_nonneg (sub_nonneg.2 hrL) hc1_4, mul_nonneg (sub_nonneg.2 hrU) hc1_4, hfn2.le, mul_nonneg hr0 hfn2.le, mul_nonneg (sub_nonneg.2 hrL) hfn2.le, mul_nonneg (sub_nonneg.2 hrU) hfn2.le, hfn2, fN201.le, mul_nonneg hr0 fN201.le, mul_nonneg (sub_nonneg.2 hrL) fN201.le, mul_nonneg (sub_nonneg.2 hrU) fN201.le, fN201, fP202, mul_nonneg hr0 fP202, mul_nonneg (sub_nonneg.2 hrL) fP202, mul_nonneg (sub_nonneg.2 hrU) fP202, hr, hr0, hrL, hrU, hru1, hrv1]) (lt_irrefl (0:ℝ))
      · have fP201 : 0 ≤ (0:ℝ) * u1 + ((1:ℝ) + ((-1:ℝ)/2) * r) * v1 + (((-7:ℝ)/4) + (1:ℝ) * r) := by dsimp only [cross3] at hP201; linarith only [hP201, hr, hru1, hrv1]
        exact absurd (close_Xb r hrs hr hrL hrU u0 v0 u1 v1 (by dsimp only [cross3]; linear_combination ((366580664:ℝ)/2735765205) * (mul_nonneg hr0 hc0_0) + ((400531000:ℝ)/547153041) * (mul_nonneg (sub_nonneg.2 hrU) hc0_1) + ((7328445545551:ℝ)/54715304100000) * hc0_2 + ((4005463369:ℝ)/5471530410) * (mul_nonneg (sub_nonneg.2 hrU) hc0_2) + ((39284000:ℝ)/547153041) * (mul_nonneg (sub_nonneg.2 hrU) fN200.le) + ((340065713:ℝ)/10943060820) * (zero_le_one : (0:ℝ) ≤ 1) + ((-19642000:ℝ)/547153041) * hru0 + ((-39284000:ℝ)/547153041) * hrv0 + ((-10778777:ℝ)/160927365) * hr) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc0_2 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc0_2)) (by dsimp only [cross3]; linear_combination ((8037:ℝ)/20000) * hc0_3 + ((3:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc0_3) + (1:ℝ) * fN200.le + (1:ℝ) * (mul_nonneg hr0 fN200.le) + ((1:ℝ)/2) * hru0 + (1:ℝ) * hrv0) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc0_3) (by dsimp only [cross3]; linear_combination ((114538763:ℝ)/1480605396) * (mul_nonneg hr0 hc0_0) + ((107764250:ℝ)/370151349) * (mul_nonneg (sub_nonneg.2 hrL) hc0_1) + ((122339625:ℝ)/246767566) * (mul_nonneg (sub_nonneg.2 hrL) hc0_2) + ((11539:ℝ)/740302698) * (mul_nonneg hr0 hc0_3) + ((131125:ℝ)/854853) * (mul_nonneg (sub_nonneg.2 hrL) fN200.le) + ((245401:ℝ)/6838824) * (zero_le_one : (0:ℝ) ≤ 1) + ((131125:ℝ)/1709706) * hru0 + ((131125:ℝ)/854853) * hrv0 + ((512305:ℝ)/6838824) * hr) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hfn2.le + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hfn2.le) + ((-1:ℝ)/2) * hru1) (by dsimp only [cross3]; linear_combination (1:ℝ) * fP201 + ((1:ℝ)/4) * hr) (by dsimp only [cross3]; linear_combination ((125:ℝ)/1616) * (mul_nonneg hr0 hc1_1) + ((93739:ℝ)/699728) * (mul_nonneg hr0 hc1_2) + ((125:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hc1_2) + ((125:ℝ)/404) * (mul_nonneg (sub_nonneg.2 hrL) fP201) + ((-125:ℝ)/808) * hrv1 + ((67:ℝ)/3232) * hr) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc1_4) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc1_0 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc1_0))) (not_le.2 hd_0_1)
    · have fP200 : 0 ≤ ((1:ℝ) + ((-1:ℝ)/2) * r) * u0 + (((3:ℝ)/2) + (-1:ℝ) * r) * v0 + (((1:ℝ)/2) + ((-1:ℝ)/4) * r) := by dsimp only [cross3] at hP200; linarith only [hP200, hr, hru0, hrv0]
      exact absurd (close_Xa r hrs hr hrL hrU u0 v0 u7 v7 (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc0_0 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc0_0) + ((58:ℝ)/433) * (mul_nonneg hr0 hc0_2) + ((375:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hc0_2)) (by dsimp only [cross3]; linear_combination ((17041:ℝ)/2735765205) * (mul_nonneg hr0 hc0_0) + ((129284000:ℝ)/547153041) * (mul_nonneg (sub_nonneg.2 hrU) hc0_1) + ((7330295652839:ℝ)/54715304100000) * hc0_2 + ((496437041:ℝ)/5471530410) * (mul_nonneg (sub_nonneg.2 hrU) hc0_2) + ((69284000:ℝ)/547153041) * (mul_nonneg (sub_nonneg.2 hrU) fP200) + ((196368877:ℝ)/10943060820) * (zero_le_one : (0:ℝ) ≤ 1) + ((34642000:ℝ)/547153041) * hru0 + ((69284000:ℝ)/547153041) * hrv0 + ((-8822527:ℝ)/643709460) * hr) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc0_1) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc0_3 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc0_3)) (by dsimp only [cross3]; linear_combination (1:ℝ) * fP200 + ((-1:ℝ)/4) * hr) (by dsimp only [cross3]; linear_combination ((58:ℝ)/433) * (mul_nonneg hr0 hc0_0) + ((375:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hc0_0)) (by dsimp only [cross3]; linear_combination ((49:ℝ)/866) * (mul_nonneg hr0 hT_0) + ((625:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hT_0) + ((2679:ℝ)/20000) * hT_1 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hT_1)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hT_0 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hT_0)) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc7_4) (by dsimp only [cross3]; linear_combination ((125:ℝ)/622) * (mul_nonneg (sub_nonneg.2 hrL) hc7_0) + ((416647:ℝ)/3110000) * hc7_1 + ((93:ℝ)/311) * (mul_nonneg (sub_nonneg.2 hrU) hc7_1) + ((61:ℝ)/1244) * (zero_le_one : (0:ℝ) ≤ 1) + ((61:ℝ)/1244) * hr) (by dsimp only [cross3]; linear_combination ((106235000:ℝ)/646437041) * (mul_nonneg (sub_nonneg.2 hrU) hc7_0) + ((1963:ℝ)/34642) * (mul_nonneg hr0 hc7_1) + ((43290611997:ℝ)/559814477506) * (mul_nonneg hr0 hc7_2) + ((1004625:ℝ)/16159993) * (mul_nonneg (sub_nonneg.2 hrL) hc7_2) + ((413395000:ℝ)/646437041) * (mul_nonneg (sub_nonneg.2 hrU) hc7_3) + ((8037:ℝ)/149284) * (zero_le_one : (0:ℝ) ≤ 1) + ((-7321:ℝ)/37321) * hr) (by dsimp only [cross3]; linear_combination ((294630000:ℝ)/819647041) * (mul_nonneg (sub_nonneg.2 hrU) hc7_0) + ((294630000:ℝ)/819647041) * (mul_nonneg (sub_nonneg.2 hrU) hc7_1) + ((2321:ℝ)/34642) * (mul_nonneg hr0 hc7_2) + ((14688418:ℝ)/819647041) * (mul_nonneg hr0 hc7_3) + ((15000:ℝ)/17321) * (mul_nonneg (sub_nonneg.2 hrU) hc7_4) + ((80455205:ℝ)/1639294082) * (mul_nonneg hr0 hT_1) + ((-31247:ℝ)/189284) * hr)) (not_le.2 hd_0_7)
  · by_contra hneg3
    push Not at hneg3
    have hfn3 : 0 < ((-1:ℝ) * r) * u1 + (1:ℝ) * v1 + (((1:ℝ)/2) + ((-1:ℝ)/2) * r) := by linarith only [hneg3]
    rcases lt_or_ge (cross3 ((((-1:ℝ)/2) + ((1:ℝ)/2) * r), ((1:ℝ)/2)) (((1:ℝ) + ((-1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (u0, v0)) 0 with hN300 | hP300
    · have fN300 : 0 < ((-1:ℝ) + ((1:ℝ)/2) * r) * u0 + (((-3:ℝ)/2) + (1:ℝ) * r) * v0 + (((-1:ℝ)/2) + ((1:ℝ)/4) * r) := by dsimp only [cross3] at hN300; linarith only [hN300, hr, hru0, hrv0]
      rcases lt_or_ge (cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) 0 with hN301 | hP301
      · have fN301 : 0 < (((3:ℝ)/2) + (-1:ℝ) * r) * u1 + ((-1:ℝ) + ((1:ℝ)/2) * r) * v1 + (((7:ℝ)/4) + (-1:ℝ) * r) := by dsimp only [cross3] at hN301; linarith only [hN301, hr, hru1, hrv1]
        exact absurd (close_Xc r hrs hr hrL hrU u1 v1 u2 v2 (by dsimp only [cross3]; linear_combination ((20000:ℝ)/47321) * (mul_nonneg (sub_nonneg.2 hrU) hc1_0) + ((2744875:ℝ)/20489993) * (mul_nonneg hr0 hc1_3) + ((125:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hc1_3) + ((7321:ℝ)/94642) * (mul_nonneg hr0 hfn3.le) + ((-7321:ℝ)/94642) * hru1 + ((-7321:ℝ)/94642) * hr) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/40000) * hfn3.le + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hfn3.le) + ((1:ℝ)/4) * hru1) (by dsimp only [cross3]; linear_combination ((29:ℝ)/1299) * (mul_nonneg hr0 hfn3.le) + ((125:ℝ)/866) * (mul_nonneg (sub_nonneg.2 hrL) hfn3.le) + ((1:ℝ)/2) * fN301.le + ((1:ℝ)/6) * (mul_nonneg hr0 fN301.le) + ((-1:ℝ)/3) * hru1 + ((1:ℝ)/12) * hrv1 + ((-1:ℝ)/4) * hr) (by dsimp only [cross3]; linear_combination ((17041:ℝ)/760740000) * (mul_nonneg hr0 hc1_0) + ((2679:ℝ)/25358) * (mul_nonneg (sub_nonneg.2 hrU) hc1_3) + ((12679:ℝ)/60000) * (mul_nonneg hr0 hc1_4) + ((2321:ℝ)/38037) * (mul_nonneg (sub_nonneg.2 hrU) hfn3.le) + ((1229:ℝ)/12990000) * (mul_nonneg hr0 fN301.le) + ((679:ℝ)/10392) * (mul_nonneg (sub_nonneg.2 hrL) fN301.le) + ((-1678877:ℝ)/380370000) * hru1 + ((1963:ℝ)/60000) * hrv1 + ((-53152549:ℝ)/1521480000) * hr) (by dsimp only [cross3]; linear_combination ((114707713:ℝ)/542788386) * (mul_nonneg hr0 hc1_0) + ((1065000:ℝ)/12923533) * (mul_nonneg (sub_nonneg.2 hrU) hc1_1) + ((440:ℝ)/271394193) * (mul_nonneg hr0 hc1_4) + ((16160000:ℝ)/271394193) * (mul_nonneg (sub_nonneg.2 hrL) hfn3.le) + ((8660000:ℝ)/271394193) * (mul_nonneg (sub_nonneg.2 hrL) fN301.le) + ((12119780:ℝ)/90464731) * (zero_le_one : (0:ℝ) ≤ 1) + ((-24820000:ℝ)/271394193) * hru1 + ((4330000:ℝ)/271394193) * hrv1 + ((-136937713:ℝ)/1085576772) * hr) (by dsimp only [cross3]; linear_combination ((183:ℝ)/866) * (mul_nonneg hr0 hc2_2) + ((125:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hc2_2)) (by dsimp only [cross3]; linear_combination ((29:ℝ)/433) * (mul_nonneg hr0 hc2_1) + ((375:ℝ)/866) * (mul_nonneg (sub_nonneg.2 hrL) hc2_1) + ((2679:ℝ)/40000) * hc2_2 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hc2_2)) (by dsimp only [cross3]; linear_combination ((1:ℝ)/4) * hc2_1 + ((2679:ℝ)/40000) * hc2_3 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hc2_3)) (by dsimp only [cross3]; linear_combination ((183:ℝ)/866) * (mul_nonneg hr0 hc2_3) + ((125:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hc2_3)) (by dsimp only [cross3]; linear_combination ((183:ℝ)/866) * (mul_nonneg hr0 hc2_0) + ((125:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hc2_0))) (not_le.2 hd_1_2)
      · have fP301 : 0 ≤ (((-3:ℝ)/2) + (1:ℝ) * r) * u1 + ((1:ℝ) + ((-1:ℝ)/2) * r) * v1 + (((-7:ℝ)/4) + (1:ℝ) * r) := by dsimp only [cross3] at hP301; linarith only [hP301, hr, hru1, hrv1]
        exact absurd (close_Xb r hrs hr hrL hrU u0 v0 u1 v1 (by dsimp only [cross3]; linear_combination ((366580664:ℝ)/2735765205) * (mul_nonneg hr0 hc0_0) + ((400531000:ℝ)/547153041) * (mul_nonneg (sub_nonneg.2 hrU) hc0_1) + ((7328445545551:ℝ)/54715304100000) * hc0_2 + ((4005463369:ℝ)/5471530410) * (mul_nonneg (sub_nonneg.2 hrU) hc0_2) + ((39284000:ℝ)/547153041) * (mul_nonneg (sub_nonneg.2 hrU) fN300.le) + ((340065713:ℝ)/10943060820) * (zero_le_one : (0:ℝ) ≤ 1) + ((-19642000:ℝ)/547153041) * hru0 + ((-39284000:ℝ)/547153041) * hrv0 + ((-10778777:ℝ)/160927365) * hr) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc0_2 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc0_2)) (by dsimp only [cross3]; linear_combination ((8037:ℝ)/20000) * hc0_3 + ((3:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc0_3) + (1:ℝ) * fN300.le + (1:ℝ) * (mul_nonneg hr0 fN300.le) + ((1:ℝ)/2) * hru0 + (1:ℝ) * hrv0) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc0_3) (by dsimp only [cross3]; linear_combination ((114538763:ℝ)/1480605396) * (mul_nonneg hr0 hc0_0) + ((107764250:ℝ)/370151349) * (mul_nonneg (sub_nonneg.2 hrL) hc0_1) + ((122339625:ℝ)/246767566) * (mul_nonneg (sub_nonneg.2 hrL) hc0_2) + ((11539:ℝ)/740302698) * (mul_nonneg hr0 hc0_3) + ((131125:ℝ)/854853) * (mul_nonneg (sub_nonneg.2 hrL) fN300.le) + ((245401:ℝ)/6838824) * (zero_le_one : (0:ℝ) ≤ 1) + ((131125:ℝ)/1709706) * hru0 + ((131125:ℝ)/854853) * hrv0 + ((512305:ℝ)/6838824) * hr) (by dsimp only [cross3]; linear_combination (1:ℝ) * fP301 + ((1:ℝ)/4) * hr) (by dsimp only [cross3]; linear_combination ((225:ℝ)/883) * (mul_nonneg (sub_nonneg.2 hrL) hc1_1) + ((7497743:ℝ)/88300000) * hc1_3 + ((1817:ℝ)/8830) * (mul_nonneg (sub_nonneg.2 hrU) hc1_3) + ((433:ℝ)/8830) * hfn3.le + ((573:ℝ)/5518750) * fP301 + ((696:ℝ)/4415) * (mul_nonneg (sub_nonneg.2 hrU) fP301) + ((-696:ℝ)/4415) * hru1 + ((348:ℝ)/4415) * hrv1 + ((-619:ℝ)/17660) * hr) (by dsimp only [cross3]; linear_combination ((778879000:ℝ)/14269735631) * (mul_nonneg (sub_nonneg.2 hrU) hc1_1) + ((4034080661:ℝ)/142697356310) * (mul_nonneg hr0 hc1_2) + ((5085748425:ℝ)/14269735631) * (mul_nonneg (sub_nonneg.2 hrL) hc1_3) + ((15082095027:ℝ)/142697356310) * (mul_nonneg hr0 hfn3.le) + ((3897304200:ℝ)/14269735631) * (mul_nonneg (sub_nonneg.2 hrL) fP301) + ((6061475811:ℝ)/71348678155) * (zero_le_one : (0:ℝ) ≤ 1) + ((23890946973:ℝ)/142697356310) * hru1 + ((-1948652100:ℝ)/14269735631) * hrv1 + ((-347949591:ℝ)/142697356310) * hr) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc1_4) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc1_0 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc1_0))) (not_le.2 hd_0_1)
    · have fP300 : 0 ≤ ((1:ℝ) + ((-1:ℝ)/2) * r) * u0 + (((3:ℝ)/2) + (-1:ℝ) * r) * v0 + (((1:ℝ)/2) + ((-1:ℝ)/4) * r) := by dsimp only [cross3] at hP300; linarith only [hP300, hr, hru0, hrv0]
      exact absurd (close_Xa r hrs hr hrL hrU u0 v0 u7 v7 (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc0_0 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc0_0) + ((58:ℝ)/433) * (mul_nonneg hr0 hc0_2) + ((375:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hc0_2)) (by dsimp only [cross3]; linear_combination ((17041:ℝ)/2735765205) * (mul_nonneg hr0 hc0_0) + ((129284000:ℝ)/547153041) * (mul_nonneg (sub_nonneg.2 hrU) hc0_1) + ((7330295652839:ℝ)/54715304100000) * hc0_2 + ((496437041:ℝ)/5471530410) * (mul_nonneg (sub_nonneg.2 hrU) hc0_2) + ((69284000:ℝ)/547153041) * (mul_nonneg (sub_nonneg.2 hrU) fP300) + ((196368877:ℝ)/10943060820) * (zero_le_one : (0:ℝ) ≤ 1) + ((34642000:ℝ)/547153041) * hru0 + ((69284000:ℝ)/547153041) * hrv0 + ((-8822527:ℝ)/643709460) * hr) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc0_1) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc0_3 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc0_3)) (by dsimp only [cross3]; linear_combination (1:ℝ) * fP300 + ((-1:ℝ)/4) * hr) (by dsimp only [cross3]; linear_combination ((58:ℝ)/433) * (mul_nonneg hr0 hc0_0) + ((375:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hc0_0)) (by dsimp only [cross3]; linear_combination ((49:ℝ)/866) * (mul_nonneg hr0 hT_0) + ((625:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hT_0) + ((2679:ℝ)/20000) * hT_1 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hT_1)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hT_0 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hT_0)) (by dsimp only [cross3]; linear_combination ((1:ℝ)/2) * hc7_4) (by dsimp only [cross3]; linear_combination ((125:ℝ)/622) * (mul_nonneg (sub_nonneg.2 hrL) hc7_0) + ((416647:ℝ)/3110000) * hc7_1 + ((93:ℝ)/311) * (mul_nonneg (sub_nonneg.2 hrU) hc7_1) + ((61:ℝ)/1244) * (zero_le_one : (0:ℝ) ≤ 1) + ((61:ℝ)/1244) * hr) (by dsimp only [cross3]; linear_combination ((106235000:ℝ)/646437041) * (mul_nonneg (sub_nonneg.2 hrU) hc7_0) + ((1963:ℝ)/34642) * (mul_nonneg hr0 hc7_1) + ((43290611997:ℝ)/559814477506) * (mul_nonneg hr0 hc7_2) + ((1004625:ℝ)/16159993) * (mul_nonneg (sub_nonneg.2 hrL) hc7_2) + ((413395000:ℝ)/646437041) * (mul_nonneg (sub_nonneg.2 hrU) hc7_3) + ((8037:ℝ)/149284) * (zero_le_one : (0:ℝ) ≤ 1) + ((-7321:ℝ)/37321) * hr) (by dsimp only [cross3]; linear_combination ((294630000:ℝ)/819647041) * (mul_nonneg (sub_nonneg.2 hrU) hc7_0) + ((294630000:ℝ)/819647041) * (mul_nonneg (sub_nonneg.2 hrU) hc7_1) + ((2321:ℝ)/34642) * (mul_nonneg hr0 hc7_2) + ((14688418:ℝ)/819647041) * (mul_nonneg hr0 hc7_3) + ((15000:ℝ)/17321) * (mul_nonneg (sub_nonneg.2 hrU) hc7_4) + ((80455205:ℝ)/1639294082) * (mul_nonneg hr0 hT_1) + ((-31247:ℝ)/189284) * hr)) (not_le.2 hd_0_7)

end CirclePackingConstants

open CirclePackingConstants in
theorem solution (p0 p1 p2 p7 : Point) (h0 : eightCell 0 p0) (h1 : eightCell 1 p1)
    (h2 : eightCell 2 p2) (h7 : eightCell 7 p7)
    (hT : 0 ≤ p7.2 ∧ 1 / 2 - eightS ≤ p7.1 + p7.2)
    (d01 : 2 - Real.sqrt 3 < sqDist p0 p1) (d12 : 2 - Real.sqrt 3 < sqDist p1 p2)
    (d07 : 2 - Real.sqrt 3 < sqDist p0 p7) (d17 : 2 - Real.sqrt 3 < sqDist p1 p7) :
    eightQuad p1 := by
  have hr : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hr0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hrL : (1.732:ℝ) ≤ Real.sqrt 3 := by nlinarith
  have hrU : Real.sqrt 3 ≤ 1.7321 := by nlinarith
  have hs : eightS = 1 - Real.sqrt 3 / 2 := by unfold eightS; ring
  have c0 : eightS ≤ p0.1 ∧ p0.1 ≤ 1 / 2 ∧ eightS ≤ p0.2 ∧ p0.2 ≤ 1 / 2 := h0
  obtain ⟨c0_0, c0_1, c0_2, c0_3⟩ := c0
  have c1 : -eightS ≤ p1.1 ∧ p1.1 ≤ eightS ∧ -p1.2 ≤ p1.1 ∧ p1.1 ≤ p1.2 ∧ p1.2 ≤ 1 / 2 := h1
  obtain ⟨c1_0, c1_1, c1_2, c1_3, c1_4⟩ := c1
  have c2 : -(1 / 2) ≤ p2.1 ∧ p2.1 ≤ -eightS ∧ eightS ≤ p2.2 ∧ p2.2 ≤ 1 / 2 := h2
  obtain ⟨c2_0, c2_1, c2_2, c2_3⟩ := c2
  have c7 : -eightS ≤ p7.2 ∧ p7.2 ≤ eightS ∧ -p7.1 ≤ p7.2 ∧ p7.2 ≤ p7.1 ∧ p7.1 ≤ 1 / 2 := h7
  obtain ⟨c7_0, c7_1, c7_2, c7_3, c7_4⟩ := c7
  have hT0 := hT.1
  have hT1 := hT.2
  have hq := chaseI_vars (Real.sqrt 3) rfl hr hr0 hrL hrU p0.1 p0.2 p1.1 p1.2 p2.1 p2.2 p7.1 p7.2
    (by linarith [c0_0, c0_1, c0_2, c0_3, hs])
    (by linarith [c0_0, c0_1, c0_2, c0_3, hs])
    (by linarith [c0_0, c0_1, c0_2, c0_3, hs])
    (by linarith [c0_0, c0_1, c0_2, c0_3, hs])
    (by linarith [c1_0, c1_1, c1_2, c1_3, c1_4, hs])
    (by linarith [c1_0, c1_1, c1_2, c1_3, c1_4, hs])
    (by linarith [c1_0, c1_1, c1_2, c1_3, c1_4, hs])
    (by linarith [c1_0, c1_1, c1_2, c1_3, c1_4, hs])
    (by linarith [c1_0, c1_1, c1_2, c1_3, c1_4, hs])
    (by linarith [c2_0, c2_1, c2_2, c2_3, hs])
    (by linarith [c2_0, c2_1, c2_2, c2_3, hs])
    (by linarith [c2_0, c2_1, c2_2, c2_3, hs])
    (by linarith [c2_0, c2_1, c2_2, c2_3, hs])
    (by linarith [c7_0, c7_1, c7_2, c7_3, c7_4, hs])
    (by linarith [c7_0, c7_1, c7_2, c7_3, c7_4, hs])
    (by linarith [c7_0, c7_1, c7_2, c7_3, c7_4, hs])
    (by linarith [c7_0, c7_1, c7_2, c7_3, c7_4, hs])
    (by linarith [c7_0, c7_1, c7_2, c7_3, c7_4, hs])
    (by linarith [hT0, hs])
    (by linarith [hT1, hs])
    d01
    d07
    d12
    d17
  obtain ⟨q0, q1, q2, q3⟩ := hq
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hs]
