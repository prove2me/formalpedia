-- Prove2me | solution 1 for Eden.not_simultaneous_rotation_returns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:13:58.203321+00:00
-- url     : https://prove2.me/submissions/bc99be98-bcb6-4844-b8c4-4afbc06730b0

import Definitions.Def_Eden_RadialReturns
import Mathlib.NumberTheory.Real.Irrational
import Definitions.Def_Eden_RotationReturns

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    ¬(Real.cos t = 1 ∧ Real.cos (Real.sqrt 2 * t) = 1) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff t).mp h₁
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff (Real.sqrt 2 * t)).mp h₂
  have hn₀ : (n : ℝ) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hn
    linarith
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (by positivity)
  have hmul : Real.sqrt 2 * (n : ℝ) = (m : ℝ) := by
    apply mul_right_cancel₀ hpi
    calc
      _ = Real.sqrt 2 * ((n : ℝ) * (2 * Real.pi)) := by ring
      _ = _ := by rw [hn]; exact hm.symm
  exact irrational_sqrt_two.ne_rational m n ((eq_div_iff hn₀).mpr hmul)
end Eden
