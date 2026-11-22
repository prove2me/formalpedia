-- Prove2me | solution 1 for Formalism.ZF.norm_integral_compl_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:19.789623+00:00
-- url     : https://prove2.me/submissions/c4de6c2d-3fe8-4b2a-bf4e-0351858aec5d

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (f : ℝ → ℂ) (B T : ℝ) (hB : 0 ≤ B) (hT : 0 < T)
    (hf : ∀ t : ℝ, T ≤ |t| → ‖f t‖ ≤ B / t ^ 2) :
    ‖∫ t in (Set.Ioc (-T) T)ᶜ, f t‖ ≤ 2 * Real.pi * B / T := by
  have hSm : MeasurableSet ((Set.Ioc (-T) T)ᶜ) := measurableSet_Ioc.compl
  have hg_int : Integrable (fun t : ℝ => 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_div hT.ne').const_mul _
  have hbound : ∀ t ∈ (Set.Ioc (-T) T)ᶜ, ‖f t‖ ≤ 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ := by
    intro t ht
    have hTt : T ≤ |t| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have ht2 : T ^ 2 ≤ t ^ 2 := by
      have := pow_le_pow_left₀ hT.le hTt 2
      rwa [sq_abs] at this
    have htpos : 0 < t ^ 2 := lt_of_lt_of_le (by positivity) ht2
    calc ‖f t‖ ≤ B / t ^ 2 := hf t hTt
      _ ≤ 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ := by
        rw [show 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ = 2 * B / (T ^ 2 + t ^ 2) by
          field_simp]
        rw [div_le_div_iff₀ htpos (by positivity)]
        nlinarith
  have h1 : ‖∫ t in (Set.Ioc (-T) T)ᶜ, f t‖ ≤ ∫ t in (Set.Ioc (-T) T)ᶜ, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ :=
    norm_integral_le_of_norm_le hg_int.integrableOn (ae_restrict_of_forall_mem hSm hbound)
  have h2 : ∫ t in (Set.Ioc (-T) T)ᶜ, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ ≤
      ∫ t, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ :=
    setIntegral_le_integral hg_int (Filter.Eventually.of_forall (fun t => by positivity))
  have h3 : ∫ t, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ = 2 * Real.pi * B / T := by
    rw [integral_const_mul]
    have e := MeasureTheory.Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) T
    rw [e, integral_univ_inv_one_add_sq, abs_of_pos hT]
    field_simp
    ring
  linarith
end Formalism.ZF
