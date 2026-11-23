-- Prove2me | solution 1 for Deduction.landau_growth_contra
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:19.417697+00:00
-- url     : https://prove2.me/submissions/5ab40b39-7b24-4ea4-86bf-5885de807677

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauGrowthContra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution {c d e C : ℝ} (hc : 0 < c) (hd : 0 < d) (hde : d < e) :
    ∃ η : ℝ, 0 < η ∧ ∃ U₀ : ℝ, ∀ U ≥ U₀, ∀ k : ℕ, U ≤ k → C * Real.exp (η * U) / e ^ k < c / d ^ k := by
  have he : 0 < e := hd.trans hde
  have hL : 0 < Real.log (e / d) := Real.log_pos ((one_lt_div hd).mpr hde)
  set L := Real.log (e / d) with hLdef
  refine ⟨L / 2, by positivity, 2 * |C| / (c * L), ?_⟩
  intro U hU k hk
  have hdk : 0 < d ^ k := pow_pos hd k
  have hek : 0 < e ^ k := pow_pos he k
  have hpow : e ^ k = d ^ k * Real.exp (k * L) := by
    rw [Real.exp_nat_mul, hLdef, Real.exp_log (div_pos he hd), div_pow, mul_div_cancel₀ _ hdk.ne']
  rw [div_lt_div_iff₀ hek hdk, hpow]
  set X := Real.exp (L / 2 * U) with hXdef
  have hXpos : 0 < X := Real.exp_pos _
  have hcL : 0 < c * L := mul_pos hc hL
  rw [ge_iff_le, div_le_iff₀ hcL] at hU
  have h1 : L / 2 * U + 1 ≤ X := Real.add_one_le_exp _
  have hX : |C| < c * X := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]
  have hY : X * X ≤ Real.exp (k * L) := by
    rw [hXdef, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hk hL.le]
  have hCX : C * X * d ^ k ≤ |C| * X * d ^ k := by
    have := le_abs_self C
    have hXd : 0 < X * d ^ k := mul_pos hXpos hdk
    nlinarith
  have h2 : |C| * X < c * (X * X) := by nlinarith
  have h3 : c * (X * X) ≤ c * Real.exp (k * L) := mul_le_mul_of_nonneg_left hY hc.le
  calc C * X * d ^ k ≤ |C| * X * d ^ k := hCX
    _ < c * Real.exp (k * L) * d ^ k := mul_lt_mul_of_pos_right (h2.trans_le h3) hdk
    _ = c * (d ^ k * Real.exp (k * L)) := by ring
end Deduction
