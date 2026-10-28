-- Prove2me | solution 1 for D1Bound5.bennett_two_scaled_radius_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:05.955542+00:00
-- url     : https://prove2.me/submissions/1a223f58-53c1-428c-a5d3-79385a2a41e1

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_bennett_two_distance_ratio_le

section
namespace D1Bound5

/-- The local radius 2u/5 gives the exact three-distance product used in the
two-anchor coefficient bound. -/
theorem bennett_two_local_radius_product (u v : ℝ) :
    (2 * u / 5) * (u - 2 * u / 5) * (v - 2 * u / 5) =
      (6 / 25 : ℝ) * u ^ 2 * (v - 2 * u / 5) := by ring









end D1Bound5
end

section
namespace D1Bound5

/-- The two possible orders of the local distances give the same rational
bound. This keeps the radius choice and the triangle inequality explicit. -/
theorem _root_.solution
    (X δ B r : ℝ) (hX : 0 < X) (hδ : 0 < δ) (hB : 0 < B)
    (hXB : X ≤ B) (hδB : δ ≤ X+B)
    (hr : r = 2*min X δ/5) :
    4*X*δ^2/(r*(X-r)*(δ-r)) ≤ (125/3 : ℝ)*B/X := by
  by_cases horder : X ≤ δ
  · have hr' : r = 2*X/5 := by simpa only [min_eq_left horder] using hr
    have hdist : 0 < δ-2*X/5 := by linarith
    have hratio := bennett_two_distance_ratio_le B X δ hB hX hXB horder hδB
    calc
      _ = (50/3 : ℝ)*(δ^2/(δ-2*X/5))/X := by
        rw [hr']
        rw [bennett_two_local_radius_product]
        field_simp [hX.ne', hdist.ne']
        <;> ring
      _ ≤ (50/3 : ℝ)*((5/2 : ℝ)*B)/X := by gcongr
      _ = _ := by ring
  · have horder' : δ ≤ X := le_of_not_ge horder
    have hr' : r = 2*δ/5 := by simpa only [min_eq_right horder'] using hr
    have hdist : 0 < X-2*δ/5 := by linarith
    have hratio := bennett_two_distance_ratio_le B δ X hB hδ
      (horder'.trans hXB) horder' (by linarith)
    have hdeneq : r*(X-r)*(δ-r) =
        (6/25 : ℝ)*δ^2*(X-2*δ/5) := by rw [hr']; ring
    calc
      _ = (50/3 : ℝ)*(X^2/(X-2*δ/5))/X := by
        rw [hdeneq]
        field_simp [hX.ne', hδ.ne', hdist.ne']
        <;> ring
      _ ≤ (50/3 : ℝ)*((5/2 : ℝ)*B)/X := by gcongr
      _ = _ := by ring



end D1Bound5
end
