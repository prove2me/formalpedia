-- Prove2me | solution 1 for BalanceSpecification.hasSum_betaDigit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:03.706044+00:00
-- url     : https://prove2.me/submissions/730ab7d5-6f0b-419a-b06c-b71be87c309d

module
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyRealization
public import Theorems.Thm_BalanceSpecification_betaDigit_zero_or_one
public import Theorems.Thm_BalanceSpecification_betaResidual_bounds
public import Theorems.Thm_BalanceSpecification_betaDigit_sum_range

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {β a x R : ℝ} (hβ : 1 < β) (ha : 0 < a)
    (hax : a ≤ x) (hxR : x ≤ R) (haR : 1 + a ≤ R) (hR : (β - 1) * R ≤ 1) :
    HasSum (fun n : ℕ => betaDigit β a x n / β ^ (n + 1)) x := by
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hnonneg n : 0 ≤ betaDigit β a x n := by
    rcases betaDigit_zero_or_one β a x n with h | h <;>
      simp only [h, zero_le_one, le_refl]
  have hupper : Tendsto (fun n : ℕ => R / β ^ n) atTop (𝓝 0) := by
    have H := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hβ0.le)
      (inv_lt_one_of_one_lt₀ hβ)).const_mul R
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using H
  have hrem : Tendsto (fun n : ℕ => betaResidual β a x n / β ^ n) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact div_nonneg (ha.le.trans (betaResidual_bounds hβ ha hax hxR haR hR n).1)
        (pow_nonneg hβ0.le n)
    · intro n
      exact div_le_div_of_nonneg_right (betaResidual_bounds hβ ha hax hxR haR hR n).2
        (pow_nonneg hβ0.le n)
    · exact hupper
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun n => div_nonneg (hnonneg n) (pow_nonneg hβ0.le _)) x).mpr
  have H : Tendsto (fun n : ℕ => x - betaResidual β a x n / β ^ n)
      atTop (𝓝 (x - 0)) := tendsto_const_nhds.sub hrem
  simpa only [betaDigit_sum_range hβ0.ne', sub_zero] using H
end BalanceSpecification
