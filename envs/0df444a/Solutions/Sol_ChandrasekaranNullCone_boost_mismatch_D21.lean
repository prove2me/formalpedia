-- Prove2me | solution 1 for ChandrasekaranNullCone.boost_mismatch_D21
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-26T15:32:07.966805+00:00
-- url     : https://prove2.me/submissions/bcbd8ad8-9bf0-49b0-8b3d-7fe96318b5da

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ChandrasekaranNullCone.BoostD21

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

end ChandrasekaranNullCone.BoostD21

open ChandrasekaranNullCone.BoostD21 in
theorem solution (c d η : ℝ) (hd : 0 < d) (G : ℝ → ℝ → ℝ)
    (hG : G (-d) d = Real.exp η * G (-d) (Real.exp η * d)) :
    let G₀ : ℝ → ℝ → ℝ := fun u u' => -c / (u - u') ^ 2
    d ^ 2 * ((G (-d) d - G₀ (-d) d) - Real.exp η * (G (-d) (Real.exp η * d) - G₀ (-d) (Real.exp η * d)))
      = c / 4 * Real.tanh (η / 2) ^ 2 := by
  intro G₀
  have he : 0 < Real.exp η := Real.exp_pos η
  have hd' : d ≠ 0 := hd.ne'
  rw [← one_sub_ratio_eq_tanh_sq]
  simp only [G₀]
  have h1 : -d - Real.exp η * d = -(d * (1 + Real.exp η)) := by ring
  have h2 : -d - d = -(2 * d) := by ring
  rw [h1, h2, hG]
  field_simp
  ring
