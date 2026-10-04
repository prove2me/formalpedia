-- Prove2me | solution 1 for CirclePackingConstants.r_n_six_lower
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-21T05:13:29.351712+00:00
-- url     : https://prove2.me/submissions/2199baf2-8478-43a9-b958-c49c66d2f0f0

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

private def delta : ℝ := Real.sqrt 13 / 6
private def scale : ℝ := 1 / (1 + delta)
private def radius : ℝ := delta / (2 * (1 + delta))

private def basePoint : Fin 6 → Point := ![
  ((0 : ℝ), (0 : ℝ)),
  ((1 : ℝ), (0 : ℝ)),
  ((1 / 2 : ℝ), (1 / 3 : ℝ)),
  ((0 : ℝ), (2 / 3 : ℝ)),
  ((1 : ℝ), (2 / 3 : ℝ)),
  ((1 / 2 : ℝ), (1 : ℝ))
]

private lemma sqrt_thirteen_pos : 0 < Real.sqrt 13 := by positivity

private lemma sqrt_thirteen_sq : (Real.sqrt 13) ^ 2 = 13 := by
  norm_num

private lemma delta_pos : 0 < delta := by
  unfold delta
  positivity

private lemma delta_sq : delta ^ 2 = (13 : ℝ) / 36 := by
  unfold delta
  rw [div_pow, sqrt_thirteen_sq]
  norm_num

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

private lemma basePoint_bounds (i : Fin 6) :
    0 ≤ (basePoint i).1 ∧ (basePoint i).1 ≤ 1 ∧
    0 ≤ (basePoint i).2 ∧ (basePoint i).2 ≤ 1 := by
  fin_cases i <;> norm_num [basePoint]

private lemma basePoint_separation (i j : Fin 6) (hij : i ≠ j) :
    (13 : ℝ) / 36 ≤ sqDist (basePoint i) (basePoint j) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [basePoint, sqDist] <;> norm_num

private def center (i : Fin 6) : Point :=
  (radius + scale * (basePoint i).1,
   radius + scale * (basePoint i).2)

private lemma scaled_sqDist (p q : Point) :
    sqDist (radius + scale * p.1, radius + scale * p.2)
      (radius + scale * q.1, radius + scale * q.2) =
      scale ^ 2 * sqDist p q := by
  unfold sqDist
  ring

private lemma center_in_inner_square (i : Fin 6) :
    InInnerSquare radius (center i) := by
  rcases basePoint_bounds i with ⟨hx0, hx1, hy0, hy1⟩
  have hs0 : 0 ≤ scale := le_of_lt scale_pos
  unfold InInnerSquare center
  dsimp
  constructor
  · nlinarith [mul_nonneg hs0 hx0]
  constructor
  · calc
      radius + scale * (basePoint i).1 ≤ radius + scale * 1 := by
        gcongr
      _ = 1 - radius := by simpa using radius_add_scale
  constructor
  · nlinarith [mul_nonneg hs0 hy0]
  · calc
      radius + scale * (basePoint i).2 ≤ radius + scale * 1 := by
        gcongr
      _ = 1 - radius := by simpa using radius_add_scale

private lemma center_separation (i j : Fin 6) (hij : i ≠ j) :
    (2 * radius) ^ 2 ≤ sqDist (center i) (center j) := by
  rw [show sqDist (center i) (center j) =
      scale ^ 2 * sqDist (basePoint i) (basePoint j) by
        exact scaled_sqDist (basePoint i) (basePoint j)]
  calc
    (2 * radius) ^ 2 = (scale * delta) ^ 2 := by rw [scale_mul_delta]
    _ = scale ^ 2 * delta ^ 2 := by ring
    _ = scale ^ 2 * ((13 : ℝ) / 36) := by rw [delta_sq]
    _ ≤ scale ^ 2 * sqDist (basePoint i) (basePoint j) := by
      exact mul_le_mul_of_nonneg_left (basePoint_separation i j hij) (sq_nonneg scale)

private lemma packable_radius : Packable 6 radius := by
  refine ⟨le_of_lt radius_pos, radius_le_half, center, ?_, ?_⟩
  · exact center_in_inner_square
  · exact center_separation

private lemma radius_le_r_n : radius ≤ r_n 6 := by
  unfold r_n
  apply le_csSup
  · refine ⟨(1 : ℝ) / 2, ?_⟩
    intro x hx
    exact hx.2.1
  · exact packable_radius

end CirclePackingConstants

theorem solution :
    (Real.sqrt 13 / 6) / (2 * (1 + Real.sqrt 13 / 6)) ≤
      CirclePackingConstants.r_n 6 := by
  exact CirclePackingConstants.radius_le_r_n
