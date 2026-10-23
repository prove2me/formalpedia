-- Prove2me | solution 1 for CODATA.normal_equations
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:13:35.19611+00:00
-- url     : https://prove2.me/submissions/f36193f3-569f-4914-b9ea-2a39cb22bfbb

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values

open CODATA

/-- one datum, one constant: `y = 0`, `u = 1`, `r = 1`, `A = 1`, `b = 0`, `G = 1`. -/
noncomputable def g80d_L : LSQ 1 1 where
  y := fun _ => 0
  u := fun _ => 1
  r := fun _ _ => 1
  A := fun _ _ => 1
  b := fun _ => 0
  G := fun _ _ => 1
  G_is_inv := by
    constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;> simp

theorem solution : ¬ (∀ {N M : ℕ} (L : LSQ N M) (hG : IsSPD L.G)
    (hA : Function.Injective L.A.mulVec) (x : Fin M → ℝ),
    (Minimizes L x ↔ SolvesNormal L x) ∧
      ∀ z, SolvesNormal L z → z = x) := by
  intro H
  have hG : IsSPD g80d_L.G := by
    refine ⟨fun i j => rfl, fun v hv => ?_⟩
    have h0 : v 0 ≠ 0 := by
      intro h; apply hv; funext i; fin_cases i; simpa using h
    simp [g80d_L]
    positivity
  have hA : Function.Injective g80d_L.A.mulVec := by
    intro v w h
    have := congrFun h 0
    simp [g80d_L, Matrix.mulVec, dotProduct] at this
    funext i; fin_cases i; simpa using this
  have hz : SolvesNormal g80d_L (fun _ => 0) := by
    intro k
    simp [resid, g80d_L, Matrix.mulVec, dotProduct]
  have := (H g80d_L hG hA (fun _ => 1)).2 _ hz
  have := congrFun this 0
  norm_num at this
