-- Prove2me | solution 1 for CirclePackingConstants.eight_chase_cells
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-06T10:19:35.653592+00:00
-- url     : https://prove2.me/submissions/5f14ca8d-d1cb-4e6a-9bd3-4095845447c0

import Definitions.Def_CirclePackingConstants
import Definitions.Def_CirclePackingConstants_Eight
import Definitions.Def_CirclePackingConstants_EightQuad
import Theorems.Thm_CirclePackingConstants_eight_hull_diam_Xf
import Theorems.Thm_CirclePackingConstants_eight_chase_I
import Theorems.Thm_CirclePackingConstants_eight_chase_II

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


theorem mem_Xf (r : ℝ) (hr : r * r = 3) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321) (u v : ℝ) (E0 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u, v)) (E1 : 0 ≤ cross3 ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)) (u, v)) (E2 : 0 ≤ cross3 ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u, v)) (E3 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) (E4 : 0 ≤ cross3 ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (u, v)) (E5 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) :
    ((u, v) : Point) ∈ convexHull ℝ ({(((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4))} : Set Point) := by
  rcases le_total (cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)) (u, v)) 0 with hn1 | hp1
  · have hT := tri_mem (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)) (u, v)
      (by have e : cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)) = (((13:ℝ)/4) + ((-15:ℝ)/8) * r) := by dsimp only [cross3]; linear_combination (1/2) * hr
          rw [e]; linarith [hrL, hrU])
      (by rw [cross3_rot]; exact E1)
      (by have e := cross3_swap23 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v) ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)); linarith [hn1])
      E0
    exact hull_mono3 ({(((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4))} : Set Point) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hT
  · rcases le_total (cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u, v)) 0 with hn2 | hp2
    · have hT := tri_mem (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u, v)
        (by have e : cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) = (((-5:ℝ)/4) + ((3:ℝ)/4) * r) := by dsimp only [cross3]; linear_combination (-1/4) * hr
            rw [e]; linarith [hrL, hrU])
        (by rw [cross3_rot]; exact E2)
        (by have e := cross3_swap23 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)); linarith [hn2])
        hp1
      exact hull_mono3 ({(((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4))} : Set Point) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) hT
    · rcases le_total (cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) 0 with hn3 | hp3
      · have hT := tri_mem (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)
          (by have e : cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) = (((7:ℝ)/2) + (-2:ℝ) * r) := by dsimp only [cross3]; linear_combination (1/2) * hr
              rw [e]; linarith [hrL, hrU])
          (by rw [cross3_rot]; exact E3)
          (by have e := cross3_swap23 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)); linarith [hn3])
          hp2
        exact hull_mono3 ({(((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4))} : Set Point) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))) hT
      · have hT := tri_mem (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (u, v)
          (by have e : cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) = (((-3:ℝ)/2) + ((7:ℝ)/8) * r) := by dsimp only [cross3]; linear_combination (-1/4) * hr
              rw [e]; linarith [hrL, hrU])
          (by rw [cross3_rot]; exact E4)
          (by have h := E5; rwa [cross3_rot] at h)
          hp3
        exact hull_mono3 ({(((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)), ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4))} : Set Point) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))) hT

set_option maxHeartbeats 4000000 in
theorem close_Xf (r : ℝ) (hrs : r = Real.sqrt 3) (hr : r * r = 3) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321)
    (u1 v1 u2 v2 : ℝ) (E0 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u1, v1)) (E1 : 0 ≤ cross3 ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)) (u1, v1)) (E2 : 0 ≤ cross3 ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u1, v1)) (E3 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) (E4 : 0 ≤ cross3 ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (u1, v1)) (E5 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1))
    (F0 : 0 ≤ cross3 (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u2, v2)) (F1 : 0 ≤ cross3 ((0:ℝ), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)) (u2, v2)) (F2 : 0 ≤ cross3 ((((1:ℝ)/2) + ((-1:ℝ)/4) * r), ((-1:ℝ)/4)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u2, v2)) (F3 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u2, v2)) (F4 : 0 ≤ cross3 ((0:ℝ), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (u2, v2)) (F5 : 0 ≤ cross3 ((((-1:ℝ)/2) + ((1:ℝ)/4) * r), ((1:ℝ)/4)) (((-1:ℝ) + ((1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u2, v2)) :
    sqDist (u1, v1) (u2, v2) ≤ 2 - r := by
  subst hrs
  exact eight_hull_diam_Xf _ (mem_Xf _ hr hrL hrU u1 v1 E0 E1 E2 E3 E4 E5) _ (mem_Xf _ hr hrL hrU u2 v2 F0 F1 F2 F3 F4 F5)

def negPt (q : Point) : Point := (-q.1, -q.2)
def permNeg : Fin 8 → Fin 8 := ![4, 5, 6, 7, 0, 1, 2, 3]

theorem sqDist_negPt (a b : Point) : sqDist (negPt a) (negPt b) = sqDist a b := by
  simp only [sqDist, negPt]; ring

theorem eightCell_neg (k : Fin 8) (q : Point) (h : eightCell (permNeg k) q) :
    eightCell k (negPt q) := by
  fin_cases k <;> simp [permNeg, eightCell, negPt] at h ⊢ <;> grind

set_option maxHeartbeats 4000000 in
theorem finalF_vars (r : ℝ) (hrs : r = Real.sqrt 3) (hr : r * r = 3) (hr0 : 0 ≤ r) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321)
    (u1 v1 u5 v5 : ℝ) (hq1_0 : 0 ≤ (-1:ℝ) * u1 + (0:ℝ) * v1 + (0:ℝ)) (hq1_1 : 0 ≤ (1:ℝ) * u1 + (1:ℝ) * v1 + (0:ℝ)) (hq1_2 : 0 ≤ ((-1:ℝ) * r) * u1 + (-1:ℝ) * v1 + ((1:ℝ) + ((-1:ℝ)/2) * r)) (hq1_3 : 0 ≤ ((1:ℝ) * r) * u1 + (-1:ℝ) * v1 + (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) (hq5_0 : 0 ≤ (1:ℝ) * u5 + (0:ℝ) * v5 + (0:ℝ)) (hq5_1 : 0 ≤ (-1:ℝ) * u5 + (-1:ℝ) * v5 + (0:ℝ)) (hq5_2 : 0 ≤ ((1:ℝ) * r) * u5 + (1:ℝ) * v5 + ((1:ℝ) + ((-1:ℝ)/2) * r)) (hq5_3 : 0 ≤ ((-1:ℝ) * r) * u5 + (1:ℝ) * v5 + (((-1:ℝ)/2) + ((1:ℝ)/2) * r)) :
    sqDist (u1, v1) (u5, v5) ≤ 2 - r := by
  have hru1 : r * r * u1 = 3 * u1 := by rw [hr]
  have hrv1 : r * r * v1 = 3 * v1 := by rw [hr]
  have hru5 : r * r * u5 = 3 * u5 := by rw [hr]
  have hrv5 : r * r * v5 = 3 * v5 := by rw [hr]
  exact close_Xf r hrs hr hrL hrU u1 v1 u5 v5 (by dsimp only [cross3]; linear_combination ((183:ℝ)/1732) * (mul_nonneg hr0 hq1_1) + ((125:ℝ)/866) * (mul_nonneg (sub_nonneg.2 hrL) hq1_1) + ((49:ℝ)/1732) * (mul_nonneg hr0 hq1_3) + ((625:ℝ)/866) * (mul_nonneg (sub_nonneg.2 hrL) hq1_3) + ((3:ℝ)/4) * hru1 + ((1:ℝ)/8) * hr) (by dsimp only [cross3]; linear_combination ((67:ℝ)/1366) * (mul_nonneg hr0 hq1_1) + ((375:ℝ)/1366) * (mul_nonneg (sub_nonneg.2 hrL) hq1_2) + ((12261:ℝ)/1182956) * (mul_nonneg hr0 hq1_3) + ((8375:ℝ)/591478) * (mul_nonneg (sub_nonneg.2 hrL) hq1_3) + ((128563:ℝ)/54640000) * (zero_le_one : (0:ℝ) ≤ 1) + ((5397:ℝ)/5464) * (sub_nonneg.2 hrU) + ((-1:ℝ)/4) * hru1 + ((-1:ℝ)/4) * hr) (by dsimp only [cross3]; linear_combination ((183:ℝ)/1732) * (mul_nonneg hr0 hq1_0) + ((125:ℝ)/866) * (mul_nonneg (sub_nonneg.2 hrL) hq1_0) + ((2679:ℝ)/40000) * hq1_1 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hq1_1) + ((49:ℝ)/2000) * (zero_le_one : (0:ℝ) ≤ 1) + ((3:ℝ)/8) * (sub_nonneg.2 hrL) + ((1:ℝ)/8) * hr) (by dsimp only [cross3]; linear_combination ((179:ℝ)/5000) * hq1_0 + (2:ℝ) * (mul_nonneg (sub_nonneg.2 hrU) hq1_0) + ((2679:ℝ)/20000) * hq1_2 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hq1_2) + ((1:ℝ)/2) * hru1) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/40000) * hq1_2 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hq1_2) + ((1:ℝ)/4) * hru1) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/40000) * hq1_3 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hq1_3) + ((-1:ℝ)/4) * hru1) (by dsimp only [cross3]; linear_combination ((179:ℝ)/5000) * hq5_0 + (2:ℝ) * (mul_nonneg (sub_nonneg.2 hrU) hq5_0) + ((2679:ℝ)/20000) * hq5_2 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) hq5_2) + ((-1:ℝ)/2) * hru5) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/40000) * hq5_2 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hq5_2) + ((-1:ℝ)/4) * hru5) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/40000) * hq5_3 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hq5_3) + ((1:ℝ)/4) * hru5) (by dsimp only [cross3]; linear_combination ((183:ℝ)/1732) * (mul_nonneg hr0 hq5_1) + ((125:ℝ)/866) * (mul_nonneg (sub_nonneg.2 hrL) hq5_1) + ((49:ℝ)/1732) * (mul_nonneg hr0 hq5_3) + ((625:ℝ)/866) * (mul_nonneg (sub_nonneg.2 hrL) hq5_3) + ((-3:ℝ)/4) * hru5 + ((1:ℝ)/8) * hr) (by dsimp only [cross3]; linear_combination ((67:ℝ)/1366) * (mul_nonneg hr0 hq5_1) + ((375:ℝ)/1366) * (mul_nonneg (sub_nonneg.2 hrL) hq5_2) + ((12261:ℝ)/1182956) * (mul_nonneg hr0 hq5_3) + ((8375:ℝ)/591478) * (mul_nonneg (sub_nonneg.2 hrL) hq5_3) + ((128563:ℝ)/54640000) * (zero_le_one : (0:ℝ) ≤ 1) + ((5397:ℝ)/5464) * (sub_nonneg.2 hrU) + ((1:ℝ)/4) * hru5 + ((-1:ℝ)/4) * hr) (by dsimp only [cross3]; linear_combination ((183:ℝ)/1732) * (mul_nonneg hr0 hq5_0) + ((125:ℝ)/866) * (mul_nonneg (sub_nonneg.2 hrL) hq5_0) + ((2679:ℝ)/40000) * hq5_1 + ((1:ℝ)/4) * (mul_nonneg (sub_nonneg.2 hrU) hq5_1) + ((49:ℝ)/2000) * (zero_le_one : (0:ℝ) ≤ 1) + ((3:ℝ)/8) * (sub_nonneg.2 hrL) + ((1:ℝ)/8) * hr)

end CirclePackingConstants

open CirclePackingConstants in
theorem solution (p : Fin 8 → Point) (hc : ∀ i, eightCell i (p i))
    (hT : 0 ≤ (p 7).2 ∧ 1 / 2 - eightS ≤ (p 7).1 + (p 7).2)
    (hd : ∀ i j, i ≠ j → 2 - Real.sqrt 3 < sqDist (p i) (p j)) : False := by
  have hr : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hr0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hrL : (1.732:ℝ) ≤ Real.sqrt 3 := by nlinarith
  have hrU : Real.sqrt 3 ≤ 1.7321 := by nlinarith
  have hs : eightS = 1 - Real.sqrt 3 / 2 := by unfold eightS; ring
  have hI := eight_chase_I (p 0) (p 1) (p 2) (p 7) (hc 0) (hc 1) (hc 2) (hc 7) hT
    (hd 0 1 (by decide)) (hd 1 2 (by decide)) (hd 0 7 (by decide)) (hd 1 7 (by decide))
  have hII := eight_chase_II (p 1) (p 3) (hc 1) (hc 3) hI (hd 1 3 (by decide))
  have hI' := eight_chase_I (negPt (p 4)) (negPt (p 5)) (negPt (p 6)) (negPt (p 3))
    (eightCell_neg 0 _ (hc 4)) (eightCell_neg 1 _ (hc 5)) (eightCell_neg 2 _ (hc 6)) (eightCell_neg 7 _ (hc 3))
    ⟨hII.1, by show 1 / 2 - eightS ≤ -(p 3).1 + -(p 3).2; linarith [hII.2]⟩
    (by rw [sqDist_negPt]; exact hd 4 5 (by decide)) (by rw [sqDist_negPt]; exact hd 5 6 (by decide))
    (by rw [sqDist_negPt]; exact hd 4 3 (by decide)) (by rw [sqDist_negPt]; exact hd 5 3 (by decide))
  obtain ⟨a0, a1, a2, a3⟩ := hI
  obtain ⟨b0, b1, b2, b3⟩ := hI'
  simp only [negPt] at b0 b1 b2 b3
  have hfin := CirclePackingConstants.finalF_vars (Real.sqrt 3) rfl hr hr0 hrL hrU (p 1).1 (p 1).2 (p 5).1 (p 5).2
    (by linarith [a0, a1, a2, a3, hs])
    (by linarith [a0, a1, a2, a3, hs])
    (by linarith [a0, a1, a2, a3, hs])
    (by linarith [a0, a1, a2, a3, hs])
    (by show 0 ≤ _; linarith [b0, b1, b2, b3, hs])
    (by show 0 ≤ _; linarith [b0, b1, b2, b3, hs])
    (by show 0 ≤ _; linarith [b0, b1, b2, b3, hs])
    (by show 0 ≤ _; linarith [b0, b1, b2, b3, hs])
  exact absurd (hd 1 5 (by decide)) (not_lt.2 hfin)
