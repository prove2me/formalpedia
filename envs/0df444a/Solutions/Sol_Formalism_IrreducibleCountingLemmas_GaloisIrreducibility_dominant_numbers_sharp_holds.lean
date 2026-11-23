-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_sharp_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:57.11251+00:00
-- url     : https://prove2.me/submissions/92719712-c3f0-446a-88b3-0fc132fe6a97

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_StretchedExponentialDominance
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_DominantNumbersEighthOfSharp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : StretchedExponentialDominance := by
  intro C ε hε
  have ha : 0 < ε / 6 := by positivity
  have hab : 0 < ε / 6 - ε / 7 := by linarith
  have hc : (0 : ℝ) < 1 / (3 * (|C| + 1)) := by positivity
  filter_upwards [(tendsto_rpow_atTop hab).eventually_ge_atTop 3,
    (isLittleO_log_rpow_atTop ha).bound hc,
    (tendsto_rpow_atTop ha).eventually_ge_atTop (3 * Real.log 20),
    Filter.eventually_ge_atTop (1 : ℝ)] with x h1 h2 h3 h4
  have hx0 : 0 < x := by linarith
  have hsplit : x ^ (ε / 6) = x ^ (ε / 7) * x ^ (ε / 6 - ε / 7) := by
    rw [← Real.rpow_add hx0]
    ring_nf
  have hb0 : 0 ≤ x ^ (ε / 7) := Real.rpow_nonneg hx0.le _
  have hxb : 3 * x ^ (ε / 7) ≤ x ^ (ε / 6) := by
    rw [hsplit]
    nlinarith
  have ha0 : 0 ≤ x ^ (ε / 6) := Real.rpow_nonneg hx0.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha0] at h2
  have hlog : C * Real.log x ≤ x ^ (ε / 6) / 3 := by
    have hC0 : 0 ≤ |C| := abs_nonneg C
    have e1 : C * Real.log x ≤ |C| * |Real.log x| := by
      rw [← abs_mul]
      exact le_abs_self _
    have e2 : |C| * |Real.log x| ≤ |C| * (1 / (3 * (|C| + 1)) * x ^ (ε / 6)) :=
      mul_le_mul_of_nonneg_left h2 hC0
    have e3 : |C| * (1 / (3 * (|C| + 1)) * x ^ (ε / 6)) ≤ x ^ (ε / 6) / 3 := by
      rw [show |C| * (1 / (3 * (|C| + 1)) * x ^ (ε / 6)) = |C| / (|C| + 1) * (x ^ (ε / 6) / 3) by
        field_simp]
      have : |C| / (|C| + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      have h6 : 0 ≤ x ^ (ε / 6) / 3 := by positivity
      nlinarith
    linarith
  have h20 : (1 : ℝ) / 20 = Real.exp (-Real.log 20) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_add, h20, ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
