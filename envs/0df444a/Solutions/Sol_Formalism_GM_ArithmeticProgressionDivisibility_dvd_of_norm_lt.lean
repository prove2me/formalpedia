-- Prove2me | solution 1 for Formalism.GM.ArithmeticProgressionDivisibility.dvd_of_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:54.428817+00:00
-- url     : https://prove2.me/submissions/a023b18c-9ce5-4630-8f37-83d786607de5

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset
open Formalism.GM.ArithmeticProgressionDivisibility
variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[p] K]
omit [NormedAlgebra ℚ_[p] K]
namespace Formalism.GM.ArithmeticProgressionDivisibility
theorem _root_.solution (k : ℤ) (i : ℕ) (hk : ‖(k : ℚ_[p])‖ < (p : ℝ) ^ (1 - (i : ℤ))) :
    (p ^ i : ℤ) ∣ k := by
  by_contra hnd
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hnd (dvd_zero _)
  have hx : (k : ℚ_[p]) ≠ 0 := by exact_mod_cast hk0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨z, hz⟩ : ∃ z : ℤ, ‖(k : ℚ_[p])‖ = (p : ℝ) ^ (-z) := by
    first
      | exact padicNormE.values_discrete hx
      | exact ⟨_, Padic.norm_eq_zpow_neg_valuation hx⟩
      | exact ⟨_, Padic.norm_eq_pow_val hx⟩
      | exact Padic.norm_values_discrete hx
  rw [hz] at hk
  have hv : -z < 1 - (i : ℤ) := (zpow_lt_zpow_iff_right₀ hp1).mp hk
  have hle : ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(i : ℤ)) := by
    rw [hz]
    exact zpow_le_zpow_right₀ hp1.le (by omega)
  have hiff : ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(i : ℤ)) ↔ (p ^ i : ℤ) ∣ k := by
    first
      | exact padicNormE.norm_int_le_pow_iff_dvd k i
      | exact Padic.norm_int_le_pow_iff_dvd k i
      | (have h0 := padicNormE.norm_int_le_pow_iff_dvd (p := p) k i; push_cast at h0; exact h0)
  exact hnd (hiff.mp hle)
end Formalism.GM.ArithmeticProgressionDivisibility
