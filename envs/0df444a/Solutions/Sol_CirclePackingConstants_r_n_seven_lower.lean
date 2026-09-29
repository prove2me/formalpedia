-- Prove2me | solution 1 for CirclePackingConstants.r_n_seven_lower
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T07:38:34.308671+00:00
-- url     : https://prove2.me/submissions/28ddb3be-456e-4cb7-a5e9-b22906b3b589

import Definitions.Def_CirclePackingConstants

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option linter.all false

noncomputable section

namespace CirclePackingConstants

private def delta : ℝ := 4 - 2 * Real.sqrt 3
private def scale : ℝ := 1 / (1 + delta)
private def radius : ℝ := delta / (2 * (1 + delta))

/-- The optimal seven-point configuration in the unit square. Six points are
pinned by the separation; the seventh is a rattler, placed here at the origin. -/
private def basePoint : Fin 7 → Point := ![
  ((0 : ℝ), (0 : ℝ)),
  ((Real.sqrt 3 - 1 : ℝ), (0 : ℝ)),
  ((2 * Real.sqrt 3 - 3 : ℝ), (2 * Real.sqrt 3 - 3 : ℝ)),
  ((1 : ℝ), (2 * Real.sqrt 3 - 3 : ℝ)),
  ((0 : ℝ), (Real.sqrt 3 - 1 : ℝ)),
  ((2 * Real.sqrt 3 - 3 : ℝ), (1 : ℝ)),
  ((1 : ℝ), (1 : ℝ))
]

private lemma sqrt3_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private lemma sqrt3_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3

private lemma sqrt3_lb : (1.73 : ℝ) < Real.sqrt 3 := by
  nlinarith [sqrt3_sq, sqrt3_nonneg]

private lemma sqrt3_ub : Real.sqrt 3 < (1.7321 : ℝ) := by
  nlinarith [sqrt3_sq, sqrt3_nonneg]

private lemma delta_sq : delta ^ 2 = 28 - 16 * Real.sqrt 3 := by
  unfold delta
  nlinarith [sqrt3_sq]

private lemma delta_pos : 0 < delta := by
  unfold delta
  nlinarith [sqrt3_ub]

private lemma scale_pos : 0 < scale := by
  unfold scale
  exact one_div_pos.mpr (by linarith [delta_pos])

private lemma radius_pos : 0 < radius := by
  unfold radius
  exact div_pos delta_pos (mul_pos (by norm_num) (by linarith [delta_pos]))

private lemma scale_mul_delta : scale * delta = 2 * radius := by
  unfold scale radius
  have h : 1 + delta ≠ 0 := ne_of_gt (by linarith [delta_pos])
  field_simp [h]

private lemma two_radius_add_scale : 2 * radius + scale = 1 := by
  unfold scale radius
  have h : 1 + delta ≠ 0 := ne_of_gt (by linarith [delta_pos])
  field_simp [h]
  ring_nf

private lemma radius_add_scale : radius + scale = 1 - radius := by
  nlinarith [two_radius_add_scale]

private lemma radius_le_half : radius ≤ (1 : ℝ) / 2 := by
  nlinarith [scale_pos, two_radius_add_scale]

private lemma basePoint_bounds (i : Fin 7) :
    0 ≤ (basePoint i).1 ∧ (basePoint i).1 ≤ 1 ∧
    0 ≤ (basePoint i).2 ∧ (basePoint i).2 ≤ 1 := by
  fin_cases i <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [basePoint, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.tail_cons, Matrix.head_fin_const, Matrix.cons_val_fin_one] <;>
    norm_num <;> nlinarith [sqrt3_lb, sqrt3_ub]

private lemma basePoint_separation (i j : Fin 7) (hij : i ≠ j) :
    (28 - 16 * Real.sqrt 3) ≤ sqDist (basePoint i) (basePoint j) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [basePoint, sqDist] <;>
    nlinarith [sqrt3_sq, sqrt3_lb, sqrt3_ub]

private def center (i : Fin 7) : Point :=
  (radius + scale * (basePoint i).1,
   radius + scale * (basePoint i).2)

private lemma scaled_sqDist (p q : Point) :
    sqDist (radius + scale * p.1, radius + scale * p.2)
      (radius + scale * q.1, radius + scale * q.2) =
      scale ^ 2 * sqDist p q := by
  unfold sqDist
  ring

private lemma center_in_inner_square (i : Fin 7) :
    InInnerSquare radius (center i) := by
  rcases basePoint_bounds i with ⟨hx0, hx1, hy0, hy1⟩
  have hs0 : 0 ≤ scale := le_of_lt scale_pos
  unfold InInnerSquare center
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hs0 hx0]
  · calc
      radius + scale * (basePoint i).1 ≤ radius + scale * 1 := by gcongr
      _ = 1 - radius := by simpa using radius_add_scale
  · nlinarith [mul_nonneg hs0 hy0]
  · calc
      radius + scale * (basePoint i).2 ≤ radius + scale * 1 := by gcongr
      _ = 1 - radius := by simpa using radius_add_scale

private lemma center_separation (i j : Fin 7) (hij : i ≠ j) :
    (2 * radius) ^ 2 ≤ sqDist (center i) (center j) := by
  rw [show sqDist (center i) (center j) =
      scale ^ 2 * sqDist (basePoint i) (basePoint j) from
        scaled_sqDist (basePoint i) (basePoint j)]
  calc
    (2 * radius) ^ 2 = (scale * delta) ^ 2 := by rw [scale_mul_delta]
    _ = scale ^ 2 * delta ^ 2 := by ring
    _ = scale ^ 2 * (28 - 16 * Real.sqrt 3) := by rw [delta_sq]
    _ ≤ scale ^ 2 * sqDist (basePoint i) (basePoint j) :=
        mul_le_mul_of_nonneg_left (basePoint_separation i j hij) (sq_nonneg scale)

private lemma packable_radius : Packable 7 radius :=
  ⟨le_of_lt radius_pos, radius_le_half, center, center_in_inner_square, center_separation⟩

private lemma radius_le_r_n : radius ≤ r_n 7 := by
  unfold r_n
  apply le_csSup
  · exact ⟨(1 : ℝ) / 2, fun x hx => hx.2.1⟩
  · exact packable_radius

end CirclePackingConstants

theorem _root_.solution :
    (4 - 2 * Real.sqrt 3) / (2 * (1 + (4 - 2 * Real.sqrt 3))) ≤
      CirclePackingConstants.r_n 7 :=
  CirclePackingConstants.radius_le_r_n

#print axioms solution
