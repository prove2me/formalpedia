-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.lg_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:19.50003+00:00
-- url     : https://prove2.me/submissions/76ee9722-50f0-4c60-8eca-251a632101bd

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_p_lt_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow


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
    (hd : d < p ^ (2 * j + 2)) : ‖(p : K) ^ j * PowerSeries.coeff d (lgF K p)‖ ≤ 1 := by
  have hp0 : (p : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnp
    exact (inv_pos.2 (by exact_mod_cast hp.pos : (0 : ℝ) < p)).ne hnp
  by_cases hc : PowerSeries.coeff d (lgF K p) = 0
  · rw [hc, mul_zero, norm_zero]; exact zero_le_one
  · obtain ⟨i, rfl⟩ := coeff_lgF_ne_zero hc
    rw [coeff_lgF_pow K hp.two_le]
    have e : (p ^ 2) ^ i = p ^ (2 * i) := by ring
    rw [e] at hd
    have hij : 2 * i < 2 * j + 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hd
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (by omega : i ≤ j)
    rw [pow_add, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_p_lt_one hp hnp).le
end Formalism.InvariantFactorPaths.G7.LemOne
