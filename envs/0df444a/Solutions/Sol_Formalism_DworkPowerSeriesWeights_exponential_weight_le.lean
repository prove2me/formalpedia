-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.exponential_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:07.23203+00:00
-- url     : https://prove2.me/submissions/37f29a59-54a7-4540-919f-0805da8f0199

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormNatCastEqOneOfNotDvd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_eq_pow_padicValNat
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGeLe_pow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_IncomingBounds_padicValFactorialBounds
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : ExpWtLe.{u, v} := by
  intro K _ _ _ l hl hlt ι r κ B hB0 hB
  classical
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have hs : PowerSeries.HasSubst B := PowerSeries.HasSubst.of_constantCoeff_zero hB0
  intro n hn
  rw [monoWtGe_iff]
  unfold mvExp
  rw [PowerSeries.coeff_subst hs]
  refine norm_finsum_le_of (Real.rpow_nonneg hpi0.le _) fun k => ?_
  rw [PowerSeries.coeff_exp, smul_eq_mul, norm_mul]
  have hk := wtGeLe_pow hpi0 hB k n hn
  rw [monoWtGe_iff] at hk
  have hfk : (k.factorial : ℕ) ≠ 0 := Nat.factorial_ne_zero k
  have hnorm : ‖(algebraMap ℚ K) (1 / (k.factorial : ℚ))‖ =
      ‖(l : K)‖ ^ (-(padicValNat l k.factorial : ℝ)) := by
    rw [map_div₀, map_one, map_natCast, norm_div, norm_one,
      norm_natCast_eq_pow_padicValNat hl hlt hfk, Real.rpow_neg hpi0.le, Real.rpow_natCast,
      one_div]
  rw [hnorm]

  have hv : (padicValNat l k.factorial : ℝ) ≤ (k : ℝ) * (1 / ((l : ℝ) - 1)) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp
    · have := (Formalism.IncomingBounds.padicValFactorialBounds l hl k hk0).2
      have hl0 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
      calc (padicValNat l k.factorial : ℝ) ≤ ((k : ℝ) - 1) / ((l : ℝ) - 1) := this
        _ ≤ (k : ℝ) / ((l : ℝ) - 1) := by
          apply div_le_div_of_nonneg_right _ hl0.le; linarith
        _ = (k : ℝ) * (1 / ((l : ℝ) - 1)) := by ring
  calc ‖(l : K)‖ ^ (-(padicValNat l k.factorial : ℝ)) * ‖MvPowerSeries.coeff n (B ^ k)‖
      ≤ ‖(l : K)‖ ^ (-(padicValNat l k.factorial : ℝ)) *
          ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r) :=
        mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hpi0.le _)
    _ = ‖(l : K)‖ ^ (-(padicValNat l k.factorial : ℝ) +
          ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r)) := by rw [← Real.rpow_add hpi0]
    _ ≤ ‖(l : K)‖ ^ (0 - dot n r) :=
        Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le (by linarith)
end Formalism.DworkPowerSeriesWeights
