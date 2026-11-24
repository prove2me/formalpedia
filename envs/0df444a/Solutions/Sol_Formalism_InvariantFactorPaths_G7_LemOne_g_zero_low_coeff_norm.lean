-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.g_zero_low_coeff_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:56.793644+00:00
-- url     : https://prove2.me/submissions/14071868-c005-4917-ae83-8c57232997b9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_p_lt_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_g0F_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_g0F_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemOne
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.LemOne
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (j d : ℕ)
    (hd : d < p ^ (2 * j + 1)) : ‖(p : K) ^ j * PowerSeries.coeff d (g0F K p)‖ ≤ 1 := by
  have hp0 : (p : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnp
    exact (inv_pos.2 (by exact_mod_cast hp.pos : (0 : ℝ) < p)).ne hnp
  by_cases hc : PowerSeries.coeff d (g0F K p) = 0
  · rw [hc, mul_zero, norm_zero]; exact zero_le_one
  · obtain ⟨i, rfl⟩ := coeff_g0F_ne_zero hc
    rw [coeff_g0F_of K hp.two_le]
    have e : p * (p ^ 2) ^ i = p ^ (2 * i + 1) := by ring
    rw [e] at hd
    have hij : 2 * i + 1 < 2 * j + 1 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hd
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (by omega : i + 1 ≤ j)
    rw [pow_add, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_p_lt_one hp hnp).le
end Formalism.InvariantFactorPaths.G7.LemOne
