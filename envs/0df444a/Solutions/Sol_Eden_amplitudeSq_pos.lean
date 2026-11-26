-- Prove2me | solution 1 for Eden.amplitudeSq_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:11.392459+00:00
-- url     : https://prove2.me/submissions/6f53597a-ca3d-4441-bd80-441a061f79a8

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
import Theorems.Thm_Eden_radialDiscriminant_pos
import Theorems.Thm_Eden_sqrt_radialDiscriminant_pos
section
noncomputable section
namespace Eden
private theorem amplitude_algebra_pos {e s R : ℝ}
    (he₀ : 0 < e) (he₁ : e ≤ 1) (hs₀ : 0 ≤ s) (hR : 0 < R)
    (hR₂ : R ^ 2 = e + (1 - e) * (s - 1) ^ 2) :
    0 < (1 + (s - 2) * (1 - e) / (R + 1)) / R := by
  have hnum : 0 < R + 1 + (s - 2) * (1 - e) := by
    rcases le_total 1 s with hs₁ | hs₁
    · have hm := mul_nonneg (sub_nonneg.mpr he₁) (sub_nonneg.mpr hs₁)
      nlinarith
    · have hsq : (s - 1) ^ 2 ≤ 1 := by nlinarith
      have hm := mul_nonneg (le_of_lt he₀) (sub_nonneg.mpr hsq)
      have hRge : 1 - s ≤ R := by nlinarith
      have hep : 0 < e * (2 - s) := mul_pos he₀ (by linarith)
      nlinarith
  have hden : 0 < R + 1 := by linarith
  have hquot : -1 < (s - 2) * (1 - e) / (R + 1) :=
    (lt_div_iff₀ hden).2 (by linarith)
  exact div_pos (by linarith) hR
end Eden
end
end

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 < amplitudeSq t s := by
  apply amplitude_algebra_pos (Real.exp_pos (-4 * t))
    (Real.exp_le_one_iff.mpr (by linarith)) hs (sqrt_radialDiscriminant_pos ht s)
  exact Real.sq_sqrt (le_of_lt (radialDiscriminant_pos ht s))
end Eden
