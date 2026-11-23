-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.logarithm_weight_induction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:23.252317+00:00
-- url     : https://prove2.me/submissions/9986fa14-6bb3-4088-8f48-94376824d2ff

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogStep
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_padicValNat_factorial_le_sub_one_div
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_coeff_exp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_coeff_truncBelow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
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
open MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff)
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : LogStep.{u, v} := by
  intro K _ _ _ l hl hπ ι r D hD0 hE
  classical
  have hπ0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  have hπ1 : ‖(l : K)‖ ≤ 1 := hπ.le
  have hD1 : Low 1 D := (low_one_iff _).2 hD0
  have hs : PowerSeries.HasSubst D := PowerSeries.HasSubst.of_constantCoeff_zero hD0
  suffices H : ∀ N, ∀ n : ι →₀ ℕ, n.degree = N →
      MonoWtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) n (coeff n D) from fun n => H _ n rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n hn
  by_cases hn0 : n = 0
  · subst hn0
    rw [monoWtGe_iff, coeff_zero_eq_constantCoeff_apply, hD0, norm_zero]
    exact Real.rpow_nonneg hπ0.le _
  have hTw : WtGe ‖(l : K)‖ r (1 / ((l : ℝ) - 1)) (truncBelow N D) := by
    intro m
    rw [monoWtGe_iff, coeff_truncBelow]
    split_ifs with hm
    · exact ih _ hm m rfl
    · simpa using Real.rpow_nonneg hπ0.le _
  have hlow : Low N (D - truncBelow N D) := by
    intro m hm
    rw [map_sub, coeff_truncBelow, if_pos hm, sub_self]
  have hT1 : Low 1 (truncBelow N D) := by
    intro m hm
    rw [coeff_truncBelow]
    split_ifs
    · exact hD1 m hm
    · rfl
  have hpow : ∀ k, Low (N + k) (D ^ (k + 1) - truncBelow N D ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simpa using hlow
    | succ k ihk =>
      have e : D ^ (k + 1 + 1) - truncBelow N D ^ (k + 1 + 1) =
          (D ^ (k + 1) - truncBelow N D ^ (k + 1)) * D +
            truncBelow N D ^ (k + 1) * (D - truncBelow N D) := by ring
      rw [e]
      exact low_add (low_mono (le_of_eq (by omega)) (low_mul ihk hD1))
        (low_mono (le_of_eq (by omega)) (low_mul (low_pow hT1 (k + 1)) hlow))

  set a : ℕ → K := fun k => PowerSeries.coeff k (PowerSeries.exp K) • coeff n (D ^ k) with ha
  have hafin : (Function.support a).Finite := PowerSeries.coeff_subst_finite hs _ n
  set b : ℕ → K := fun k => if k = 1 then 0 else a k with hb
  set c : ℕ → K := fun k => if k = 1 then a 1 else 0 with hc
  have hbfin : (Function.support b).Finite :=
    hafin.subset fun k hk => by
      simp only [Function.mem_support, hb] at hk ⊢
      split_ifs at hk with h
      · exact absurd rfl hk
      · exact hk
  have hcfin : (Function.support c).Finite :=
    (Set.finite_singleton 1).subset fun k hk => by
      simp only [Function.mem_support, hc] at hk
      split_ifs at hk with h
      · exact h
      · exact absurd rfl hk
  have habc : a = fun k => b k + c k := by
    funext k
    simp only [hb, hc]
    split_ifs with h
    · subst h; simp
    · simp
  have ha1 : a 1 = coeff n D := by
    simp [ha, PowerSeries.coeff_exp]
  have hsum : coeff n (mvExp D) = (∑ᶠ k, b k) + coeff n D := by
    unfold mvExp
    rw [PowerSeries.coeff_subst hs]
    change ∑ᶠ k, a k = _
    rw [habc, finsum_add_distrib hbfin hcfin, finsum_eq_single c 1 (fun k hk => if_neg hk)]
    simp only [hc, if_pos rfl, ha1]
  have hEq : coeff n D = coeff n (mvExp D - 1) + -(∑ᶠ k, b k) := by
    rw [map_sub, coeff_one, if_neg hn0, sub_zero, hsum]
    ring
  rw [monoWtGe_iff, hEq]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hE n) ?_)
  rw [norm_neg]
  refine norm_finsum_le_of (Real.rpow_nonneg hπ0.le _) fun k => ?_
  simp only [hb]
  split_ifs with hk1
  · simpa using Real.rpow_nonneg hπ0.le _
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk0 : k = 0 := by omega
    subst hk0
    simp only [ha, pow_zero, coeff_one, if_neg hn0, smul_zero, norm_zero]
    exact Real.rpow_nonneg hπ0.le _

  have hce : coeff n (D ^ k) = coeff n (truncBelow N D ^ k) := by
    have := hpow (k - 1) n (by omega)
    rw [Nat.sub_add_cancel (by omega), map_sub, sub_eq_zero] at this
    exact this
  have hbd := wtGe_pow hπ0 hTw k n
  rw [monoWtGe_iff] at hbd
  have hv := padicValNat_factorial_le_sub_one_div hl (k := k) (by omega)
  simp only [ha]
  rw [smul_eq_mul, norm_mul, norm_coeff_exp hl hπ, hce]
  set v := padicValNat l k.factorial
  calc (‖(l : K)‖ ^ v)⁻¹ * ‖coeff n (truncBelow N D ^ k)‖
      ≤ (‖(l : K)‖ ^ v)⁻¹ * ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r) :=
        mul_le_mul_of_nonneg_left hbd (inv_nonneg.2 (pow_nonneg hπ0.le _))
    _ = ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r - (v : ℝ)) := by
        rw [Real.rpow_sub hπ0 _ (v : ℝ), Real.rpow_natCast]
        ring
    _ ≤ ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - dot n r) := by
        apply Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1
        nlinarith
end Formalism.DworkPowerSeriesWeights
