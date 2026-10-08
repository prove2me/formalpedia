-- Prove2me | solution 1 for CirclePackingConstants.eight_four_points_in_diamond
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-06T09:09:34.463983+00:00
-- url     : https://prove2.me/submissions/39611fc6-c5a5-41a7-a9ff-cfa2be93cba4

import Definitions.Def_CirclePackingConstants
import Definitions.Def_CirclePackingConstants_Eight
import Theorems.Thm_CirclePackingConstants_eight_chase_cells
import Theorems.Thm_CirclePackingConstants_eight_hull_diam_arm7

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


theorem mem_arm7 (r : ℝ) (hr : r * r = 3) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321) (u v : ℝ) (E0 : 0 ≤ cross3 ((0:ℝ), (0:ℝ)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u, v)) (E1 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u, v)) (E2 : 0 ≤ cross3 (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) (E3 : 0 ≤ cross3 (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) (E4 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), (0:ℝ)) (u, v)) :
    ((u, v) : Point) ∈ convexHull ℝ ({((0:ℝ), (0:ℝ)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)), (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r))} : Set Point) := by
  rcases le_total (cross3 ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u, v)) 0 with hn1 | hp1
  · have hT := tri_mem ((0:ℝ), (0:ℝ)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u, v)
      (by have e : cross3 ((0:ℝ), (0:ℝ)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)) = (((-5:ℝ)/4) + ((3:ℝ)/4) * r) := by dsimp only [cross3]; linear_combination (-1/4) * hr
          rw [e]; linarith [hrL, hrU])
      (by rw [cross3_rot]; exact E1)
      (by have e := cross3_swap23 ((0:ℝ), (0:ℝ)) (u, v) (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)); linarith [hn1])
      E0
    exact hull_mono3 ({((0:ℝ), (0:ℝ)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)), (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r))} : Set Point) ((0:ℝ), (0:ℝ)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hT
  · rcases le_total (cross3 ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)) 0 with hn2 | hp2
    · have hT := tri_mem ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)
        (by have e : cross3 ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) = ((1:ℝ) + ((-1:ℝ)/2) * r) := by dsimp only [cross3]; ring
            rw [e]; linarith [hrL, hrU])
        (by rw [cross3_rot]; exact E2)
        (by have e := cross3_swap23 ((0:ℝ), (0:ℝ)) (u, v) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)); linarith [hn2])
        hp1
      exact hull_mono3 ({((0:ℝ), (0:ℝ)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)), (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r))} : Set Point) ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) hT
    · have hT := tri_mem ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u, v)
        (by have e : cross3 ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) = (((-5:ℝ)/4) + ((3:ℝ)/4) * r) := by dsimp only [cross3]; linear_combination (-1/4) * hr
            rw [e]; linarith [hrL, hrU])
        (by rw [cross3_rot]; exact E3)
        (by have h := E4; rwa [cross3_rot] at h)
        hp2
      exact hull_mono3 ({((0:ℝ), (0:ℝ)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)), (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)), (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)), (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r))} : Set Point) ((0:ℝ), (0:ℝ)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))) hT

set_option maxHeartbeats 4000000 in
theorem close_arm7 (r : ℝ) (hrs : r = Real.sqrt 3) (hr : r * r = 3) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321)
    (u1 v1 u2 v2 : ℝ) (E0 : 0 ≤ cross3 ((0:ℝ), (0:ℝ)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u1, v1)) (E1 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u1, v1)) (E2 : 0 ≤ cross3 (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) (E3 : 0 ≤ cross3 (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u1, v1)) (E4 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), (0:ℝ)) (u1, v1))
    (F0 : 0 ≤ cross3 ((0:ℝ), (0:ℝ)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u2, v2)) (F1 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)) (u2, v2)) (F2 : 0 ≤ cross3 (((1:ℝ)/2), ((-1:ℝ) + ((1:ℝ)/2) * r)) (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u2, v2)) (F3 : 0 ≤ cross3 (((1:ℝ)/2), ((1:ℝ) + ((-1:ℝ)/2) * r)) (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) (u2, v2)) (F4 : 0 ≤ cross3 (((1:ℝ) + ((-1:ℝ)/2) * r), ((1:ℝ) + ((-1:ℝ)/2) * r)) ((0:ℝ), (0:ℝ)) (u2, v2)) :
    sqDist (u1, v1) (u2, v2) ≤ 2 - r := by
  subst hrs
  exact eight_hull_diam_arm7 _ (mem_arm7 _ hr hrL hrU u1 v1 E0 E1 E2 E3 E4) _ (mem_arm7 _ hr hrL hrU u2 v2 F0 F1 F2 F3 F4)

set_option maxHeartbeats 4000000 in
theorem cell7_close_vars (r : ℝ) (hrs : r = Real.sqrt 3) (hr : r * r = 3) (hr0 : 0 ≤ r) (hrL : (1.732:ℝ) ≤ r) (hrU : r ≤ 1.7321)
    (u1 v1 u2 v2 : ℝ) (h1_0 : 0 ≤ (0:ℝ) * u1 + (1:ℝ) * v1 + ((1:ℝ) + ((-1:ℝ)/2) * r)) (h1_1 : 0 ≤ (0:ℝ) * u1 + (-1:ℝ) * v1 + ((1:ℝ) + ((-1:ℝ)/2) * r)) (h1_2 : 0 ≤ (1:ℝ) * u1 + (-1:ℝ) * v1 + (0:ℝ)) (h1_3 : 0 ≤ (1:ℝ) * u1 + (1:ℝ) * v1 + (0:ℝ)) (h1_4 : 0 ≤ (-1:ℝ) * u1 + (0:ℝ) * v1 + ((1:ℝ)/2)) (h2_0 : 0 ≤ (0:ℝ) * u2 + (1:ℝ) * v2 + ((1:ℝ) + ((-1:ℝ)/2) * r)) (h2_1 : 0 ≤ (0:ℝ) * u2 + (-1:ℝ) * v2 + ((1:ℝ) + ((-1:ℝ)/2) * r)) (h2_2 : 0 ≤ (1:ℝ) * u2 + (-1:ℝ) * v2 + (0:ℝ)) (h2_3 : 0 ≤ (1:ℝ) * u2 + (1:ℝ) * v2 + (0:ℝ)) (h2_4 : 0 ≤ (-1:ℝ) * u2 + (0:ℝ) * v2 + ((1:ℝ)/2)) :
    sqDist (u1, v1) (u2, v2) ≤ 2 - r := by
  have hr1' : (1.73:ℝ) < r := by linarith
  have hr2' : r < (1.74:ℝ) := by linarith
  have hru1 : r * r * u1 = 3 * u1 := by rw [hr]
  have hrv1 : r * r * v1 = 3 * v1 := by rw [hr]
  have hru2 : r * r * u2 = 3 * u2 := by rw [hr]
  have hrv2 : r * r * v2 = 3 * v2 := by rw [hr]
  exact close_arm7 r hrs hr hrL hrU u1 v1 u2 v2 (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * h1_3 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) h1_3)) (by dsimp only [cross3]; linear_combination ((183:ℝ)/866) * (mul_nonneg hr0 h1_0) + ((125:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) h1_0)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/10000) * h1_4 + (1:ℝ) * (mul_nonneg (sub_nonneg.2 hrU) h1_4)) (by dsimp only [cross3]; linear_combination ((183:ℝ)/866) * (mul_nonneg hr0 h1_1) + ((125:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) h1_1)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * h1_2 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) h1_2)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * h2_3 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) h2_3)) (by dsimp only [cross3]; linear_combination ((183:ℝ)/866) * (mul_nonneg hr0 h2_0) + ((125:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) h2_0)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/10000) * h2_4 + (1:ℝ) * (mul_nonneg (sub_nonneg.2 hrU) h2_4)) (by dsimp only [cross3]; linear_combination ((183:ℝ)/866) * (mul_nonneg hr0 h2_1) + ((125:ℝ)/433) * (mul_nonneg (sub_nonneg.2 hrL) h2_1)) (by dsimp only [cross3]; linear_combination ((2679:ℝ)/20000) * h2_2 + ((1:ℝ)/2) * (mul_nonneg (sub_nonneg.2 hrU) h2_2))

end CirclePackingConstants


open CirclePackingConstants

namespace CirclePackingConstants

def rotPt (q : Point) : Point := (q.2, -q.1)
def reflPt (q : Point) : Point := (q.1, -q.2)
def permRot : Fin 8 → Fin 8 := ![2, 3, 4, 5, 6, 7, 0, 1]
def permRefl : Fin 8 → Fin 8 := ![6, 5, 4, 3, 2, 1, 0, 7]

theorem sqDist_rotPt (a b : Point) : sqDist (rotPt a) (rotPt b) = sqDist a b := by
  simp only [sqDist, rotPt]; ring
theorem sqDist_reflPt (a b : Point) : sqDist (reflPt a) (reflPt b) = sqDist a b := by
  simp only [sqDist, reflPt]; ring

theorem permRot_injective : Function.Injective permRot := by decide
theorem permRefl_injective : Function.Injective permRefl := by decide

theorem eightCell_rot (k : Fin 8) (q : Point) (h : eightCell (permRot k) q) :
    eightCell k (rotPt q) := by
  fin_cases k <;> simp [permRot, eightCell, rotPt] at h ⊢ <;> grind

theorem eightCell_refl (k : Fin 8) (q : Point) (h : eightCell (permRefl k) q) :
    eightCell k (reflPt q) := by
  fin_cases k <;> simp [permRefl, eightCell, reflPt] at h ⊢ <;> grind

theorem arm7_in_diamond (p : Fin 8 → Point) (hc : ∀ i, eightCell i (p i))
    (hd : ∀ i j, i ≠ j → 2 - Real.sqrt 3 < sqDist (p i) (p j)) :
    |(p 7).1| + |(p 7).2| ≤ (Real.sqrt 3 - 1) / 2 := by
  by_contra hout'
  have hout := not_le.1 hout'
  have hs : eightS = 1 - Real.sqrt 3 / 2 := by unfold eightS; ring
  have c7 := hc 7
  have c7' : -eightS ≤ (p 7).2 ∧ (p 7).2 ≤ eightS ∧ -(p 7).1 ≤ (p 7).2 ∧ (p 7).2 ≤ (p 7).1 ∧
      (p 7).1 ≤ 1 / 2 := c7
  obtain ⟨a1, a2, a3, a4, a5⟩ := c7'
  rcases le_total 0 (p 7).2 with hv | hv
  · refine eight_chase_cells p hc ⟨hv, ?_⟩ hd
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hv] at hout
    linarith
  · refine eight_chase_cells (fun k => reflPt (p (permRefl k))) (fun k => eightCell_refl k _ (hc _))
      ⟨?_, ?_⟩ (fun i j hij => ?_)
    · show 0 ≤ -(p 7).2
      linarith
    · show 1 / 2 - eightS ≤ (p 7).1 + -(p 7).2
      rw [abs_of_nonneg (by linarith), abs_of_nonpos hv] at hout
      linarith
    · rw [sqDist_reflPt]
      exact hd _ _ (fun e => hij (permRefl_injective e))

theorem rot_config (p : Fin 8 → Point) (hc : ∀ i, eightCell i (p i))
    (hd : ∀ i j, i ≠ j → 2 - Real.sqrt 3 < sqDist (p i) (p j)) :
    (∀ i, eightCell i ((fun k => rotPt (p (permRot k))) i)) ∧
    (∀ i j, i ≠ j → 2 - Real.sqrt 3 < sqDist ((fun k => rotPt (p (permRot k))) i)
      ((fun k => rotPt (p (permRot k))) j)) := by
  refine ⟨fun k => eightCell_rot k _ (hc _), fun i j hij => ?_⟩
  show 2 - Real.sqrt 3 < sqDist (rotPt (p (permRot i))) (rotPt (p (permRot j)))
  rw [sqDist_rotPt]
  exact hd _ _ (fun e => hij (permRot_injective e))

theorem arm_in_diamond (p : Fin 8 → Point) (hc : ∀ i, eightCell i (p i))
    (hd : ∀ i j, i ≠ j → 2 - Real.sqrt 3 < sqDist (p i) (p j)) (a : Fin 8)
    (ha : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7) :
    |(p a).1| + |(p a).2| ≤ (Real.sqrt 3 - 1) / 2 := by
  rcases ha with rfl | rfl | rfl | rfl
  · obtain ⟨h1, h2⟩ := rot_config p hc hd
    have := arm7_in_diamond _ h1 h2
    simpa [rotPt, permRot, add_comm] using this
  · obtain ⟨h1, h2⟩ := rot_config p hc hd
    obtain ⟨h3, h4⟩ := rot_config _ h1 h2
    have := arm7_in_diamond _ h3 h4
    simpa [rotPt, permRot] using this
  · obtain ⟨h1, h2⟩ := rot_config p hc hd
    obtain ⟨h3, h4⟩ := rot_config _ h1 h2
    obtain ⟨h5, h6⟩ := rot_config _ h3 h4
    have := arm7_in_diamond _ h5 h6
    simpa [rotPt, permRot, add_comm] using this
  · exact arm7_in_diamond p hc hd

end CirclePackingConstants



open CirclePackingConstants

namespace CirclePackingConstants

theorem sqrt3_facts : Real.sqrt 3 * Real.sqrt 3 = 3 ∧ 0 ≤ Real.sqrt 3 ∧ (1.732:ℝ) ≤ Real.sqrt 3 ∧
    Real.sqrt 3 ≤ 1.7321 ∧ eightS = 1 - Real.sqrt 3 / 2 := by
  have hr : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hr0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  refine ⟨hr, hr0, by nlinarith, by nlinarith, by unfold eightS; ring⟩

theorem cell7_close (a b : Point) (ha : eightCell 7 a) (hb : eightCell 7 b) :
    sqDist a b ≤ 2 - Real.sqrt 3 := by
  obtain ⟨hr, hr0, hrL, hrU, hs⟩ := sqrt3_facts
  have ha' : -eightS ≤ a.2 ∧ a.2 ≤ eightS ∧ -a.1 ≤ a.2 ∧ a.2 ≤ a.1 ∧ a.1 ≤ 1 / 2 := ha
  have hb' : -eightS ≤ b.2 ∧ b.2 ≤ eightS ∧ -b.1 ≤ b.2 ∧ b.2 ≤ b.1 ∧ b.1 ≤ 1 / 2 := hb
  obtain ⟨a0, a1, a2, a3, a4⟩ := ha'
  obtain ⟨b0, b1, b2, b3, b4⟩ := hb'
  exact cell7_close_vars (Real.sqrt 3) rfl hr hr0 hrL hrU a.1 a.2 b.1 b.2
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)

theorem cell0_close (a b : Point) (ha : eightCell 0 a) (hb : eightCell 0 b) :
    sqDist a b ≤ 2 - Real.sqrt 3 := by
  obtain ⟨hr, hr0, hrL, hrU, hs⟩ := sqrt3_facts
  have ha' : eightS ≤ a.1 ∧ a.1 ≤ 1 / 2 ∧ eightS ≤ a.2 ∧ a.2 ≤ 1 / 2 := ha
  have hb' : eightS ≤ b.1 ∧ b.1 ≤ 1 / 2 ∧ eightS ≤ b.2 ∧ b.2 ≤ 1 / 2 := hb
  obtain ⟨a0, a1, a2, a3⟩ := ha'
  obtain ⟨b0, b1, b2, b3⟩ := hb'
  unfold sqDist
  have h1 : (a.1 - b.1) ^ 2 ≤ (1 / 2 - eightS) ^ 2 := by nlinarith
  have h2 : (a.2 - b.2) ^ 2 ≤ (1 / 2 - eightS) ^ 2 := by nlinarith
  have h3 : 2 * (1 / 2 - eightS) ^ 2 = 2 - Real.sqrt 3 := by rw [hs]; nlinarith
  linarith

theorem cell_close (j : Fin 8) (a b : Point) (ha : eightCell j a) (hb : eightCell j b) :
    sqDist a b ≤ 2 - Real.sqrt 3 := by
  fin_cases j
  · exact cell0_close a b ha hb
  · have := cell7_close (rotPt a) (rotPt b) (eightCell_rot 7 a (by simpa [permRot] using ha))
      (eightCell_rot 7 b (by simpa [permRot] using hb))
    rwa [sqDist_rotPt] at this
  · have h := cell0_close (rotPt a) (rotPt b) (eightCell_rot 0 a (by simpa [permRot] using ha))
      (eightCell_rot 0 b (by simpa [permRot] using hb))
    rwa [sqDist_rotPt] at h
  · have h1 := eightCell_rot 1 a (by simpa [permRot] using ha)
    have h2 := eightCell_rot 1 b (by simpa [permRot] using hb)
    have := cell7_close (rotPt (rotPt a)) (rotPt (rotPt b))
      (eightCell_rot 7 _ (by simpa [permRot] using h1)) (eightCell_rot 7 _ (by simpa [permRot] using h2))
    rwa [sqDist_rotPt, sqDist_rotPt] at this
  · have h1 := eightCell_rot 2 a (by simpa [permRot] using ha)
    have h2 := eightCell_rot 2 b (by simpa [permRot] using hb)
    have := cell0_close (rotPt (rotPt a)) (rotPt (rotPt b))
      (eightCell_rot 0 _ (by simpa [permRot] using h1)) (eightCell_rot 0 _ (by simpa [permRot] using h2))
    rwa [sqDist_rotPt, sqDist_rotPt] at this
  · have h1 := eightCell_rot 3 a (by simpa [permRot] using ha)
    have h2 := eightCell_rot 3 b (by simpa [permRot] using hb)
    have h1' := eightCell_rot 1 _ (by simpa [permRot] using h1)
    have h2' := eightCell_rot 1 _ (by simpa [permRot] using h2)
    have := cell7_close (rotPt (rotPt (rotPt a))) (rotPt (rotPt (rotPt b)))
      (eightCell_rot 7 _ (by simpa [permRot] using h1')) (eightCell_rot 7 _ (by simpa [permRot] using h2'))
    rwa [sqDist_rotPt, sqDist_rotPt, sqDist_rotPt] at this
  · have h1 := eightCell_rot 4 a (by simpa [permRot] using ha)
    have h2 := eightCell_rot 4 b (by simpa [permRot] using hb)
    have h1' := eightCell_rot 2 _ (by simpa [permRot] using h1)
    have h2' := eightCell_rot 2 _ (by simpa [permRot] using h2)
    have := cell0_close (rotPt (rotPt (rotPt a))) (rotPt (rotPt (rotPt b)))
      (eightCell_rot 0 _ (by simpa [permRot] using h1')) (eightCell_rot 0 _ (by simpa [permRot] using h2'))
    rwa [sqDist_rotPt, sqDist_rotPt, sqDist_rotPt] at this
  · exact cell7_close a b ha hb

end CirclePackingConstants



open CirclePackingConstants

namespace CirclePackingConstants

noncomputable def idxPt (q : Point) : Fin 8 :=
  if eightS ≤ q.1 ∧ eightS ≤ q.2 then 0
  else if q.1 ≤ -eightS ∧ eightS ≤ q.2 then 2
  else if q.1 ≤ -eightS ∧ q.2 ≤ -eightS then 4
  else if eightS ≤ q.1 ∧ q.2 ≤ -eightS then 6
  else if q.2 ≤ q.1 ∧ -q.2 ≤ q.1 then 7
  else if q.1 ≤ q.2 ∧ -q.1 ≤ q.2 then 1
  else if q.1 ≤ -q.2 ∧ q.1 ≤ q.2 then 3
  else 5

theorem idx_spec (q : Point) (h1 : |q.1| ≤ 1 / 2) (h2 : |q.2| ≤ 1 / 2) : eightCell (idxPt q) q := by
  obtain ⟨_, _, _, _, hs⟩ := sqrt3_facts
  have hS : eightS ≤ 1 / 2 := by rw [hs]; nlinarith [Real.sqrt_nonneg 3, Real.mul_self_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  have hS0 : 0 ≤ eightS := by rw [hs]; nlinarith [Real.sqrt_nonneg 3, Real.mul_self_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  unfold idxPt
  split_ifs with c0 c2 c4 c6 c7 c1 c3
  · show eightS ≤ q.1 ∧ q.1 ≤ 1 / 2 ∧ eightS ≤ q.2 ∧ q.2 ≤ 1 / 2
    grind
  · show -(1 / 2) ≤ q.1 ∧ q.1 ≤ -eightS ∧ eightS ≤ q.2 ∧ q.2 ≤ 1 / 2
    grind
  · show -(1 / 2) ≤ q.1 ∧ q.1 ≤ -eightS ∧ -(1 / 2) ≤ q.2 ∧ q.2 ≤ -eightS
    grind
  · show eightS ≤ q.1 ∧ q.1 ≤ 1 / 2 ∧ -(1 / 2) ≤ q.2 ∧ q.2 ≤ -eightS
    grind
  · show -eightS ≤ q.2 ∧ q.2 ≤ eightS ∧ -q.1 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ 1 / 2
    grind
  · show -eightS ≤ q.1 ∧ q.1 ≤ eightS ∧ -q.2 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ 1 / 2
    grind
  · show -eightS ≤ q.2 ∧ q.2 ≤ eightS ∧ q.1 ≤ -q.2 ∧ q.1 ≤ q.2 ∧ -(1 / 2) ≤ q.1
    grind
  · show -eightS ≤ q.1 ∧ q.1 ≤ eightS ∧ q.2 ≤ -q.1 ∧ q.2 ≤ q.1 ∧ -(1 / 2) ≤ q.2
    grind


theorem B_main : ∀ p : Fin 8 → Point,
    (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
    (∀ i j, i ≠ j → 2 - Real.sqrt 3 < sqDist (p i) (p j)) →
    ∃ q : Fin 4 → Fin 8, Function.Injective q ∧
      ∀ k, |(p (q k)).1 - 1 / 2| + |(p (q k)).2 - 1 / 2| ≤ (Real.sqrt 3 - 1) / 2 := by
  intro p hp hd
  let c : Fin 8 → Point := fun i => ((p i).1 - 1 / 2, (p i).2 - 1 / 2)
  have hcd : ∀ i j, sqDist (c i) (c j) = sqDist (p i) (p j) := by
    intro i j; simp only [c, sqDist]; ring
  have hbox : ∀ i, |(c i).1| ≤ 1 / 2 ∧ |(c i).2| ≤ 1 / 2 := by
    intro i
    obtain ⟨a, b, c', d⟩ := hp i
    exact ⟨abs_le.2 ⟨by simp only [c]; linarith, by simp only [c]; linarith⟩,
      abs_le.2 ⟨by simp only [c]; linarith, by simp only [c]; linarith⟩⟩
  have hspec : ∀ i, eightCell (idxPt (c i)) (c i) := fun i => idx_spec (c i) (hbox i).1 (hbox i).2
  have hinj : Function.Injective (fun i => idxPt (c i)) := by
    intro i j hij
    by_contra hne
    have h1 := hspec i
    have h2 : eightCell (idxPt (c i)) (c j) := by
      have := hspec j
      simp only at hij
      rw [← hij] at this
      exact this
    have := cell_close _ _ _ h1 h2
    rw [hcd] at this
    exact absurd (hd i j hne) (not_lt.2 this)
  have hbij := Finite.injective_iff_bijective.1 hinj
  let g : Fin 8 → Fin 8 := Function.surjInv hbij.2
  have hg : ∀ j, idxPt (c (g j)) = j := Function.surjInv_eq hbij.2
  have ginj : Function.Injective g := Function.injective_surjInv hbij.2
  have hc : ∀ j, eightCell j ((fun j => c (g j)) j) := by
    intro j
    have := hspec (g j)
    rw [hg j] at this
    exact this
  have hd' : ∀ i j, i ≠ j → 2 - Real.sqrt 3 < sqDist ((fun j => c (g j)) i) ((fun j => c (g j)) j) := by
    intro i j hij
    show 2 - Real.sqrt 3 < sqDist (c (g i)) (c (g j))
    rw [hcd]
    exact hd _ _ (fun e => hij (ginj e))
  refine ⟨fun k => g (![1, 3, 5, 7] k), ?_, ?_⟩
  · intro a b hab
    have := ginj hab
    revert this
    fin_cases a <;> fin_cases b <;> simp
  · intro k
    have hk : (![1, 3, 5, 7] k : Fin 8) = 1 ∨ (![1, 3, 5, 7] k : Fin 8) = 3 ∨
        (![1, 3, 5, 7] k : Fin 8) = 5 ∨ (![1, 3, 5, 7] k : Fin 8) = 7 := by
      fin_cases k <;> simp
    have := arm_in_diamond (fun j => c (g j)) hc hd' _ hk
    exact this

end CirclePackingConstants


open CirclePackingConstants in
theorem solution : ∀ p : Fin 8 → Point,
    (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
    (∀ i j, i ≠ j → 2 - Real.sqrt 3 < sqDist (p i) (p j)) →
    ∃ q : Fin 4 → Fin 8, Function.Injective q ∧
      ∀ k, |(p (q k)).1 - 1 / 2| + |(p (q k)).2 - 1 / 2| ≤ (Real.sqrt 3 - 1) / 2 := B_main
