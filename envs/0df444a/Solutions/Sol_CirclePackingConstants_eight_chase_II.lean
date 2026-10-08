-- Prove2me | solution 1 for CirclePackingConstants.eight_chase_II
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-06T10:19:34.556205+00:00
-- url     : https://prove2.me/submissions/0ff08a15-4aa7-4b8e-a7cf-38e5d170a481

import Definitions.Def_CirclePackingConstants
import Definitions.Def_CirclePackingConstants_Eight
import Definitions.Def_CirclePackingConstants_EightQuad
import Theorems.Thm_CirclePackingConstants_eight_hull_diam_Xd

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


theorem mem_Xd (r : ℝ) (hr : r * r = 3) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321) (u v : ℝ) (E0 : 0 ≤ cross3 (((-1:ℝ)/2), (0:ℝ)) ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u, v)) (E1 : 0 ≤ cross3 ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u, v)) (E2 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((0:ℝ), (0:ℝ)) (u, v)) (E3 : 0 ≤ cross3 ((0:ℝ), (0:ℝ)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) (E4 : 0 ≤ cross3 ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (u, v)) (E5 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) (E6 : 0 ≤ cross3 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ)/2), (0:ℝ)) (u, v)) :
    ((u, v) : Point) ∈ convexHull ℝ ({(((-1:ℝ)/2), (0:ℝ)), ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((0:ℝ), (0:ℝ)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)), (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r))} : Set Point) := by
  rcases le_total (cross3 (((-1:ℝ)/2), (0:ℝ)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u, v)) 0 with hn1 | hp1
  · have hT := tri_mem (((-1:ℝ)/2), (0:ℝ)) ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u, v)
      (by have e : cross3 (((-1:ℝ)/2), (0:ℝ)) ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) = (((-19:ℝ)/4) + ((11:ℝ)/4) * r) := by dsimp only [cross3]; linear_combination (-3/4) * hr
          rw [e]; linarith [hrL, hrU])
      (by rw [cross3_rot]; exact E1)
      (by have e := cross3_swap23 (((-1:ℝ)/2), (0:ℝ)) (u, v) (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)); linarith [hn1])
      E0
    exact hull_mono3 ({(((-1:ℝ)/2), (0:ℝ)), ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((0:ℝ), (0:ℝ)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)), (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r))} : Set Point) (((-1:ℝ)/2), (0:ℝ)) ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hT
  · rcases le_total (cross3 (((-1:ℝ)/2), (0:ℝ)) ((0:ℝ), (0:ℝ)) (u, v)) 0 with hn2 | hp2
    · have hT := tri_mem (((-1:ℝ)/2), (0:ℝ)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((0:ℝ), (0:ℝ)) (u, v)
        (by have e : cross3 (((-1:ℝ)/2), (0:ℝ)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((0:ℝ), (0:ℝ)) = (((1:ℝ)/2) + ((-1:ℝ)/4) * r) := by dsimp only [cross3]; ring
            rw [e]; linarith [hrL, hrU])
        (by rw [cross3_rot]; exact E2)
        (by have e := cross3_swap23 (((-1:ℝ)/2), (0:ℝ)) (u, v) ((0:ℝ), (0:ℝ)); linarith [hn2])
        hp1
      exact hull_mono3 ({(((-1:ℝ)/2), (0:ℝ)), ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((0:ℝ), (0:ℝ)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)), (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r))} : Set Point) (((-1:ℝ)/2), (0:ℝ)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((0:ℝ), (0:ℝ)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) hT
    · rcases le_total (cross3 (((-1:ℝ)/2), (0:ℝ)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) 0 with hn3 | hp3
      · have hT := tri_mem (((-1:ℝ)/2), (0:ℝ)) ((0:ℝ), (0:ℝ)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)
          (by have e : cross3 (((-1:ℝ)/2), (0:ℝ)) ((0:ℝ), (0:ℝ)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) = (((1:ℝ)/2) + ((-1:ℝ)/4) * r) := by dsimp only [cross3]; ring
              rw [e]; linarith [hrL, hrU])
          (by rw [cross3_rot]; exact E3)
          (by have e := cross3_swap23 (((-1:ℝ)/2), (0:ℝ)) (u, v) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)); linarith [hn3])
          hp2
        exact hull_mono3 ({(((-1:ℝ)/2), (0:ℝ)), ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((0:ℝ), (0:ℝ)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)), (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r))} : Set Point) (((-1:ℝ)/2), (0:ℝ)) ((0:ℝ), (0:ℝ)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))) hT
      · rcases le_total (cross3 (((-1:ℝ)/2), (0:ℝ)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (u, v)) 0 with hn4 | hp4
        · have hT := tri_mem (((-1:ℝ)/2), (0:ℝ)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (u, v)
            (by have e : cross3 (((-1:ℝ)/2), (0:ℝ)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) = (((1:ℝ)/2) + ((-1:ℝ)/4) * r) := by dsimp only [cross3]; linear_combination (1/8) * hr
                rw [e]; linarith [hrL, hrU])
            (by rw [cross3_rot]; exact E4)
            (by have e := cross3_swap23 (((-1:ℝ)/2), (0:ℝ)) (u, v) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)); linarith [hn4])
            hp3
          exact hull_mono3 ({(((-1:ℝ)/2), (0:ℝ)), ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((0:ℝ), (0:ℝ)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)), (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r))} : Set Point) (((-1:ℝ)/2), (0:ℝ)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))) hT
        · have hT := tri_mem (((-1:ℝ)/2), (0:ℝ)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)
            (by have e : cross3 (((-1:ℝ)/2), (0:ℝ)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) = (((-3:ℝ)/8) + ((1:ℝ)/4) * r) := by dsimp only [cross3]; linear_combination (-1/8) * hr
                rw [e]; linarith [hrL, hrU])
            (by rw [cross3_rot]; exact E5)
            (by have h := E6; rwa [cross3_rot] at h)
            hp4
          exact hull_mono3 ({(((-1:ℝ)/2), (0:ℝ)), ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((0:ℝ), (0:ℝ)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)), (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r))} : Set Point) (((-1:ℝ)/2), (0:ℝ)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))))) hT

set_option maxHeartbeats 4000000 in
theorem close_Xd (r : ℝ) (hrs : r = Real.sqrt 3) (hr : r * r = 3) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321)
    (u1 v1 u2 v2 : ℝ) (E0 : 0 ≤ cross3 (((-1:ℝ)/2), (0:ℝ)) ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u1, v1)) (E1 : 0 ≤ cross3 ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u1, v1)) (E2 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((0:ℝ), (0:ℝ)) (u1, v1)) (E3 : 0 ≤ cross3 ((0:ℝ), (0:ℝ)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) (E4 : 0 ≤ cross3 ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (u1, v1)) (E5 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) (E6 : 0 ≤ cross3 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ)/2), (0:ℝ)) (u1, v1))
    (F0 : 0 ≤ cross3 (((-1:ℝ)/2), (0:ℝ)) ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u2, v2)) (F1 : 0 ≤ cross3 ((((3:ℝ)/2) + (-1:ℝ) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u2, v2)) (F2 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((0:ℝ), (0:ℝ)) (u2, v2)) (F3 : 0 ≤ cross3 ((0:ℝ), (0:ℝ)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u2, v2)) (F4 : 0 ≤ cross3 ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (u2, v2)) (F5 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u2, v2)) (F6 : 0 ≤ cross3 (((-1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((-1:ℝ)/2), (0:ℝ)) (u2, v2)) :
    sqDist (u1, v1) (u2, v2) ≤ 2 - r := by
  subst hrs
  exact eight_hull_diam_Xd _ (mem_Xd _ hr hrL hrU u1 v1 E0 E1 E2 E3 E4 E5 E6) _ (mem_Xd _ hr hrL hrU u2 v2 F0 F1 F2 F3 F4 F5 F6)

set_option maxHeartbeats 40000000 in
theorem chaseII_vars (r : ℝ) (hrs : r = Real.sqrt 3) (hr : r * r = 3) (hr0 : 0 ≤ r) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321)
    (u1 v1 u3 v3 : ℝ)
    (hc1_0 : 0 ≤ (1:ℝ) * u1 + (0:ℝ) * v1 + ((1:ℝ) + ((-1:ℝ)/2) * r))
    (hc1_1 : 0 ≤ (-1:ℝ) * u1 + (0:ℝ) * v1 + ((1:ℝ) + ((-1:ℝ)/2) * r))
    (hc1_2 : 0 ≤ (-1:ℝ) * u1 + (1:ℝ) * v1 + (0:ℝ))
    (hc1_3 : 0 ≤ (1:ℝ) * u1 + (1:ℝ) * v1 + (0:ℝ))
    (hc1_4 : 0 ≤ (0:ℝ) * u1 + (-1:ℝ) * v1 + ((1:ℝ)/2))
    (hq1_0 : 0 ≤ (-1:ℝ) * u1 + (0:ℝ) * v1 + (0:ℝ))
    (hq1_1 : 0 ≤ (1:ℝ) * u1 + (1:ℝ) * v1 + (0:ℝ))
    (hq1_2 : 0 ≤ ((-1:ℝ) * r) * u1 + (-1:ℝ) * v1 + ((1:ℝ) + ((-1:ℝ)/2) * r))
    (hq1_3 : 0 ≤ ((1:ℝ) * r) * u1 + (-1:ℝ) * v1 + (((-1:ℝ)/2) + ((1:ℝ)/2) * r))
    (hc3_0 : 0 ≤ (0:ℝ) * u3 + (1:ℝ) * v3 + ((1:ℝ) + ((-1:ℝ)/2) * r))
    (hc3_1 : 0 ≤ (0:ℝ) * u3 + (-1:ℝ) * v3 + ((1:ℝ) + ((-1:ℝ)/2) * r))
    (hc3_2 : 0 ≤ (-1:ℝ) * u3 + (-1:ℝ) * v3 + (0:ℝ))
    (hc3_3 : 0 ≤ (-1:ℝ) * u3 + (1:ℝ) * v3 + (0:ℝ))
    (hc3_4 : 0 ≤ (1:ℝ) * u3 + (0:ℝ) * v3 + ((1:ℝ)/2))
    (hd_1_3 : 2 - r < sqDist (u1, v1) (u3, v3))
    : 0 ≤ (0:ℝ) * u3 + (-1:ℝ) * v3 + (0:ℝ) ∧ 0 ≤ (-1:ℝ) * u3 + (-1:ℝ) * v3 + (((1:ℝ)/2) + ((-1:ℝ)/2) * r) := by
  have hru1 : r * r * u1 = 3 * u1 := by rw [hr]
  have hrv1 : r * r * v1 = 3 * v1 := by rw [hr]
  have hru3 : r * r * u3 = 3 * u3 := by rw [hr]
  have hrv3 : r * r * v3 = 3 * v3 := by rw [hr]
  refine ⟨?_, ?_⟩
  · by_contra hneg0
    push Not at hneg0
    have hfn0 : 0 < (0:ℝ) * u3 + (1:ℝ) * v3 + (0:ℝ) := by linarith only [hneg0]
    exact absurd (close_Xd r hrs hr hrL hrU u1 v1 u3 v3 (by dsimp only [cross3]; linear_combination ((915007:ℝ)/13660000) * hc1_2 + ((433:ℝ)/1366) * (mul_nonneg (sub_nonneg.2 hrU) hc1_2) + ((2744757:ℝ)/13660000) * hc1_3 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc1_3) + ((125:ℝ)/683) * (mul_nonneg (sub_nonneg.2 hrL) hq1_3) + ((183:ℝ)/2732) * (zero_le_one : (0:ℝ) ≤ 1) + ((125:ℝ)/683) * hru1 + ((125:ℝ)/1366) * hr) (by dsimp only [cross3]; linear_combination ((23995375:ℝ)/27990243) * (mul_nonneg (sub_nonneg.2 hrL) hc1_1) + ((152518601:ℝ)/5386566764) * (mul_nonneg hr0 hc1_2) + ((7287502625:ℝ)/12119775219) * (mul_nonneg (sub_nonneg.2 hrL) hc1_2) + ((3170285:ℝ)/111960972) * (mul_nonneg hr0 hc1_3) + ((23570000:ℝ)/27990243) * (mul_nonneg (sub_nonneg.2 hrU) hq1_3) + ((489595:ℝ)/37320324) * (zero_le_one : (0:ℝ) ≤ 1) + ((-23570000:ℝ)/27990243) * hru1 + ((-3720007:ℝ)/37320324) * hr) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc1_2 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc1_2)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hq1_0 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hq1_0)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/40000) * hq1_2 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hq1_2) + ((1:ℝ)/4) * hru1) (by dsimp only [cross3]; linear_combination ((183:ℝ)/1732) * (mul_nonneg hr0 hq1_2) + ((125:ℝ)/866) * (mul_nonneg (sub_nonneg.2 hrL) hq1_2) + ((1:ℝ)/4) * hq1_3 + ((-1:ℝ)/4) * hru1) (by dsimp only [cross3]; linear_combination ((2107100:ℝ)/22941443) * (mul_nonneg (sub_nonneg.2 hrL) hc1_1) + ((3248243:ℝ)/114707215) * (mul_nonneg hr0 hc1_3) + ((2890500:ℝ)/22941443) * (mul_nonneg (sub_nonneg.2 hrU) hq1_2) + ((2812255813:ℝ)/99336448190) * (mul_nonneg hr0 hq1_3) + ((2503317525:ℝ)/19867289638) * (mul_nonneg (sub_nonneg.2 hrL) hq1_3) + ((6428247:ℝ)/131093960) * (zero_le_one : (0:ℝ) ≤ 1) + ((32153243:ℝ)/114707215) * hru1 + ((3088249:ℝ)/32773490) * hr) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc3_4 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc3_4) + ((2679:ℝ)/10000) * hfn0.le + (1:ℝ) * (mul_nonneg (sub_nonneg.2 hrU) hfn0.le)) (by dsimp only [cross3]; linear_combination ((49:ℝ)/866) * (mul_nonneg hr0 hc3_0) + ((625:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hc3_0)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc3_3 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc3_3)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/40000) * hc3_2 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hc3_2) + ((2679:ℝ)/40000) * hc3_3 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hc3_3)) (by dsimp only [cross3]; linear_combination ((148210000:ℝ)/819647041) * (mul_nonneg (sub_nonneg.2 hrU) hc3_1) + ((7321:ℝ)/138568) * (mul_nonneg hr0 hc3_2) + ((40204177259:ℝ)/2839257350024) * (mul_nonneg hr0 hc3_3) + ((2209875:ℝ)/20489993) * (mul_nonneg (sub_nonneg.2 hrL) hc3_3) + ((266512500:ℝ)/819647041) * (mul_nonneg (sub_nonneg.2 hrU) hc3_4) + ((29393877:ℝ)/3278588164) * (zero_le_one : (0:ℝ) ≤ 1) + ((-226807041:ℝ)/6557176328) * hr) (by dsimp only [cross3]; linear_combination ((1:ℝ)/4) * (mul_nonneg hr0 hc3_1) + ((29:ℝ)/433) * (mul_nonneg hr0 hc3_4) + ((375:ℝ)/866) * (mul_nonneg (sub_nonneg.2 hrL) hc3_4)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc3_4 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc3_4))) (not_le.2 hd_1_3)
  · by_contra hneg1
    push Not at hneg1
    have hfn1 : 0 < (1:ℝ) * u3 + (1:ℝ) * v3 + (((-1:ℝ)/2) + ((1:ℝ)/2) * r) := by linarith only [hneg1]
    exact absurd (close_Xd r hrs hr hrL hrU u1 v1 u3 v3 (by dsimp only [cross3]; linear_combination ((915007:ℝ)/13660000) * hc1_2 + ((433:ℝ)/1366) * (mul_nonneg (sub_nonneg.2 hrU) hc1_2) + ((2744757:ℝ)/13660000) * hc1_3 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc1_3) + ((125:ℝ)/683) * (mul_nonneg (sub_nonneg.2 hrL) hq1_3) + ((183:ℝ)/2732) * (zero_le_one : (0:ℝ) ≤ 1) + ((125:ℝ)/683) * hru1 + ((125:ℝ)/1366) * hr) (by dsimp only [cross3]; linear_combination ((23995375:ℝ)/27990243) * (mul_nonneg (sub_nonneg.2 hrL) hc1_1) + ((152518601:ℝ)/5386566764) * (mul_nonneg hr0 hc1_2) + ((7287502625:ℝ)/12119775219) * (mul_nonneg (sub_nonneg.2 hrL) hc1_2) + ((3170285:ℝ)/111960972) * (mul_nonneg hr0 hc1_3) + ((23570000:ℝ)/27990243) * (mul_nonneg (sub_nonneg.2 hrU) hq1_3) + ((489595:ℝ)/37320324) * (zero_le_one : (0:ℝ) ≤ 1) + ((-23570000:ℝ)/27990243) * hru1 + ((-3720007:ℝ)/37320324) * hr) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc1_2 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc1_2)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hq1_0 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hq1_0)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/40000) * hq1_2 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hq1_2) + ((1:ℝ)/4) * hru1) (by dsimp only [cross3]; linear_combination ((183:ℝ)/1732) * (mul_nonneg hr0 hq1_2) + ((125:ℝ)/866) * (mul_nonneg (sub_nonneg.2 hrL) hq1_2) + ((1:ℝ)/4) * hq1_3 + ((-1:ℝ)/4) * hru1) (by dsimp only [cross3]; linear_combination ((2107100:ℝ)/22941443) * (mul_nonneg (sub_nonneg.2 hrL) hc1_1) + ((3248243:ℝ)/114707215) * (mul_nonneg hr0 hc1_3) + ((2890500:ℝ)/22941443) * (mul_nonneg (sub_nonneg.2 hrU) hq1_2) + ((2812255813:ℝ)/99336448190) * (mul_nonneg hr0 hq1_3) + ((2503317525:ℝ)/19867289638) * (mul_nonneg (sub_nonneg.2 hrL) hq1_3) + ((6428247:ℝ)/131093960) * (zero_le_one : (0:ℝ) ≤ 1) + ((32153243:ℝ)/114707215) * hru1 + ((3088249:ℝ)/32773490) * hr) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc3_0 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc3_0) + ((2679:ℝ)/20000) * hfn1.le + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hfn1.le)) (by dsimp only [cross3]; linear_combination ((49:ℝ)/866) * (mul_nonneg hr0 hc3_0) + ((625:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) hc3_0)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc3_3 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc3_3)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/40000) * hc3_2 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hc3_2) + ((2679:ℝ)/40000) * hc3_3 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hc3_3)) (by dsimp only [cross3]; linear_combination ((148210000:ℝ)/819647041) * (mul_nonneg (sub_nonneg.2 hrU) hc3_1) + ((7321:ℝ)/138568) * (mul_nonneg hr0 hc3_2) + ((40204177259:ℝ)/2839257350024) * (mul_nonneg hr0 hc3_3) + ((2209875:ℝ)/20489993) * (mul_nonneg (sub_nonneg.2 hrL) hc3_3) + ((266512500:ℝ)/819647041) * (mul_nonneg (sub_nonneg.2 hrU) hc3_4) + ((29393877:ℝ)/3278588164) * (zero_le_one : (0:ℝ) ≤ 1) + ((-226807041:ℝ)/6557176328) * hr) (by dsimp only [cross3]; linear_combination ((1:ℝ)/4) * (mul_nonneg hr0 hc3_1) + ((29:ℝ)/433) * (mul_nonneg hr0 hc3_4) + ((375:ℝ)/866) * (mul_nonneg (sub_nonneg.2 hrL) hc3_4)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * hc3_4 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hc3_4))) (not_le.2 hd_1_3)

end CirclePackingConstants

open CirclePackingConstants in
theorem solution (p1 p3 : Point) (h1 : eightCell 1 p1) (h3 : eightCell 3 p3)
    (hq : eightQuad p1) (d13 : 2 - Real.sqrt 3 < sqDist p1 p3) :
    0 ≤ -p3.2 ∧ 1 / 2 - eightS ≤ -p3.1 - p3.2 := by
  have hr : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hr0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hrL : (1.732:ℝ) ≤ Real.sqrt 3 := by nlinarith
  have hrU : Real.sqrt 3 ≤ 1.7321 := by nlinarith
  have hs : eightS = 1 - Real.sqrt 3 / 2 := by unfold eightS; ring
  have c1 : -eightS ≤ p1.1 ∧ p1.1 ≤ eightS ∧ -p1.2 ≤ p1.1 ∧ p1.1 ≤ p1.2 ∧ p1.2 ≤ 1 / 2 := h1
  obtain ⟨c1_0, c1_1, c1_2, c1_3, c1_4⟩ := c1
  have c3 : -eightS ≤ p3.2 ∧ p3.2 ≤ eightS ∧ p3.1 ≤ -p3.2 ∧ p3.1 ≤ p3.2 ∧ -(1 / 2) ≤ p3.1 := h3
  obtain ⟨c3_0, c3_1, c3_2, c3_3, c3_4⟩ := c3
  obtain ⟨hq0, hq1, hq2, hq3⟩ := hq
  have hv := chaseII_vars (Real.sqrt 3) rfl hr hr0 hrL hrU p1.1 p1.2 p3.1 p3.2
    (by linarith [c1_0, c1_1, c1_2, c1_3, c1_4, hs])
    (by linarith [c1_0, c1_1, c1_2, c1_3, c1_4, hs])
    (by linarith [c1_0, c1_1, c1_2, c1_3, c1_4, hs])
    (by linarith [c1_0, c1_1, c1_2, c1_3, c1_4, hs])
    (by linarith [c1_0, c1_1, c1_2, c1_3, c1_4, hs])
    (by linarith [hq0, hq1, hq2, hq3, hs])
    (by linarith [hq0, hq1, hq2, hq3, hs])
    (by linarith [hq0, hq1, hq2, hq3, hs])
    (by linarith [hq0, hq1, hq2, hq3, hs])
    (by linarith [c3_0, c3_1, c3_2, c3_3, c3_4, hs])
    (by linarith [c3_0, c3_1, c3_2, c3_3, c3_4, hs])
    (by linarith [c3_0, c3_1, c3_2, c3_3, c3_4, hs])
    (by linarith [c3_0, c3_1, c3_2, c3_3, c3_4, hs])
    (by linarith [c3_0, c3_1, c3_2, c3_3, c3_4, hs])
    d13
  obtain ⟨v0, v1⟩ := hv
  exact ⟨by linarith, by linarith [hs]⟩
