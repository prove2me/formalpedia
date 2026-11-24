-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.unitAt_of_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:24:01.790937+00:00
-- url     : https://prove2.me/submissions/a48e8d54-a170-4906-b7f5-0e0ae9b5390c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_C
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Ser
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.E.Ser
theorem _root_.solution {k : ℕ} {f : K⟦X⟧} (hf : IntS f) (h0 : ∀ i, i < k → coeff i f = 0)
    (hk : ‖coeff k f‖ = 1) : UnitAt k f := by
  obtain ⟨h, rfl⟩ := X_pow_dvd_iff.mpr h0
  have hc : ∀ d, coeff (d + k) (X ^ k * h) = coeff d h := fun d => coeff_X_pow_mul h k d
  have hk' : coeff k (X ^ k * h) = constantCoeff h := by
    have := hc 0
    rwa [zero_add, coeff_zero_eq_constantCoeff_apply] at this
  rw [hk'] at hk
  have hne : constantCoeff h ≠ 0 := by
    intro h3
    rw [h3, norm_zero] at hk
    exact zero_ne_one hk
  refine ⟨constantCoeff h, C (constantCoeff h)⁻¹ * h, hk, ⟨?_, ?_⟩, ?_⟩
  · rw [map_mul, constantCoeff_C, inv_mul_cancel₀ hne]
  · refine intS_mul (intS_C ?_) ?_
    · rw [norm_inv, hk, inv_one]
    · intro d
      rw [← hc d]
      exact hf _
  · have : C (constantCoeff h) * C (constantCoeff h)⁻¹ = (1 : K⟦X⟧) := by
      rw [← map_mul, mul_inv_cancel₀ hne, map_one]
    calc X ^ k * h = (C (constantCoeff h) * C (constantCoeff h)⁻¹) * (X ^ k * h) := by
          rw [this, one_mul]
      _ = _ := by ring
end Formalism.L2.Th1.E.Ser
