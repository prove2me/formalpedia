-- Prove2me | solution 1 for ChandrasekaranNullCone.vacuum_boost_ratio_5_29
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-26T15:31:31.943578+00:00
-- url     : https://prove2.me/submissions/9d8ca52c-83b3-49d0-9707-fb2d6b3d9e6d

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ChandrasekaranNullCone.Boost

/-- `1 - 4e^η/(1+e^η)² = tanh²(η/2)`. -/
lemma one_sub_ratio_eq_tanh_sq (η : ℝ) :
    1 - 4 * Real.exp η / (1 + Real.exp η) ^ 2 = Real.tanh (η / 2) ^ 2 := by
  have ht : 0 < Real.exp (η / 2) := Real.exp_pos _
  have he : Real.exp η = Real.exp (η / 2) * Real.exp (η / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hn : Real.exp (-(η / 2)) = (Real.exp (η / 2))⁻¹ := Real.exp_neg _
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, hn, he]
  field_simp
  ring

/-- `e^η G₀(-d, e^η d) / G₀(-d, d) = 4e^η/(1+e^η)²` for `G₀(u,u') = -c/(u-u')²`. -/
lemma vacuum_ratio (c d η : ℝ) (hc : 0 < c) (hd : 0 < d) :
    Real.exp η * (-c / (-d - Real.exp η * d) ^ 2) / (-c / (-d - d) ^ 2)
      = 4 * Real.exp η / (1 + Real.exp η) ^ 2 := by
  have he : 0 < Real.exp η := Real.exp_pos η
  have h1 : -d - Real.exp η * d = -(d * (1 + Real.exp η)) := by ring
  have h2 : -d - d = -(2 * d) := by ring
  rw [h1, h2]
  field_simp
  ring

end ChandrasekaranNullCone.Boost

open ChandrasekaranNullCone.Boost in
theorem solution (c d η : ℝ) (hc : 0 < c) (hd : 0 < d) :
    let G₀ : ℝ → ℝ → ℝ := fun u u' => -c / (u - u') ^ 2
    Real.exp η * G₀ (-d) (Real.exp η * d) / G₀ (-d) d = 4 * Real.exp η / (1 + Real.exp η) ^ 2 ∧
      1 - 4 * Real.exp η / (1 + Real.exp η) ^ 2 = Real.tanh (η / 2) ^ 2 :=
  ⟨vacuum_ratio c d η hc hd, one_sub_ratio_eq_tanh_sq η⟩
