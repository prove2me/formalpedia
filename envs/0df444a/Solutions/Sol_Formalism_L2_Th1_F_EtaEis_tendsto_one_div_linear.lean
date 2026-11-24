-- Prove2me | solution 1 for Formalism.L2.Th1.F.EtaEis.tendsto_one_div_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:24:06.069628+00:00
-- url     : https://prove2.me/submissions/e0c56625-4c8c-4176-894a-e39bb9377fb5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EtaEis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EtaEis
namespace Formalism.L2.Th1.F.EtaEis
theorem _root_.solution (c w : ℂ) (hw : w ≠ 0) :
    Tendsto (fun N : ℕ => 1 / (c + (N : ℂ) * w)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℂ))⁻¹) atTop (𝓝 0) := by
    first
    | exact RCLike.tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)
    | (have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_nhds_zero_nat
       simpa using h)
    | (rw [Metric.tendsto_atTop]
       intro ε hε
       obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
       refine ⟨K, fun n hn => ?_⟩
       have hKpos : (0 : ℝ) < 1 / ε := by positivity
       have hn' : (1 / ε : ℝ) < n := lt_of_lt_of_le hK (by exact_mod_cast hn)
       have hnpos : (0 : ℝ) < n := lt_trans hKpos hn'
       have hnorm : ‖((n : ℂ))⁻¹‖ = ((n : ℝ))⁻¹ := by simp
       rw [dist_zero_right, hnorm, inv_eq_one_div, div_lt_iff₀ hnpos]
       rw [div_lt_iff₀ hε] at hn'
       linarith)
  have h2 : Tendsto (fun N : ℕ => c * ((N : ℂ))⁻¹ + w) atTop (𝓝 (c * 0 + w)) :=
    (hinv.const_mul c).add_const w
  rw [mul_zero, zero_add] at h2
  have h3 : Tendsto (fun N : ℕ => ((N : ℂ))⁻¹ * (c * ((N : ℂ))⁻¹ + w)⁻¹) atTop (𝓝 (0 * w⁻¹)) :=
    hinv.mul (h2.inv₀ hw)
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [one_div, ← mul_inv]
  congr 1
  linear_combination c * mul_inv_cancel₀ hN0
end Formalism.L2.Th1.F.EtaEis
