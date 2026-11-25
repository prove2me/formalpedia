-- Prove2me | solution 1 for Formalism.ZF.ComplexPowerDifferenceIntegral.one_lt_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:09.965016+00:00
-- url     : https://prove2.me/submissions/e7349c0b-a486-4e64-a1a9-1e36b1d7ab5b

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_DzDifferentiableOn
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaOneEqOneSubOfRePos
import Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_partial_dz
import Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_summable_norm_dz


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.ComplexPowerDifferenceIntegral
namespace Formalism.ZF.ComplexPowerDifferenceIntegral
theorem _root_.solution {s : ℂ} (hs : 1 < s.re) : (s - 1) * riemannZeta s = s - Dz s := by
  have hs0 : 0 < s.re := by linarith
  have hsum : Summable (dz s) := (summable_norm_dz hs0).of_norm
  have hf : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    exact hf.hasSum
  have hG : HasSum (fun i : ℕ => ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s)) (riemannZeta s - 1) := by
    have h1 := (hasSum_nat_add_iff' 1).mpr hz
    have e : ∀ i : ℕ, ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s) = 1 / (((i + 1 : ℕ) : ℂ) + 1) ^ s := by
      intro i
      have : ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) = (((i + 1 : ℕ) : ℂ) + 1) := by push_cast; ring
      rw [this, cpow_neg, one_div]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, one_cpow, div_one] at h1
    have hfun : (fun i : ℕ => ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s)) =
        (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s) := funext e
    rw [hfun]
    exact h1
  have hc : Tendsto (fun N : ℕ => (((N : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hN : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hp : 0 < s.re - 1 := by linarith
    have := (tendsto_rpow_neg_atTop hp).comp hN
    refine this.congr (fun N => ?_)
    simp only [Function.comp]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    congr 1
    rw [Complex.sub_re, Complex.one_re]
    ring
  have hD : Tendsto (fun N => ∑ i ∈ Finset.range N, dz s i) atTop
      (𝓝 (Dz s)) :=
    hsum.hasSum.tendsto_sum_nat
  have hR : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, dz s i) atTop
      (𝓝 (1 - 0 - (s - 1) * (riemannZeta s - 1))) := by
    have := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).sub hc).sub
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => s - 1) atTop (𝓝 (s - 1))).mul hG.tendsto_sum_nat)
    refine this.congr (fun N => ?_)
    exact (partial_dz s N).symm
  have hlim := tendsto_nhds_unique hD hR
  rw [hlim]
  ring
end Formalism.ZF.ComplexPowerDifferenceIntegral
