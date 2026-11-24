-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.exp_jet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:08:25.95556+00:00
-- url     : https://prove2.me/submissions/f8575602-181c-4aae-8684-f81a7d47e880

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_pairExp_apply
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_pairExp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_quad_pow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of


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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (r : ℝ) (hr : 1 ≤ r) (ι : Type) [Fintype ι] (S : K) (u : ι → K) (hS : ‖S‖ ≤ r)
    (hu : ∀ i, ‖u i‖ ≤ 1) (κ : (Bool × ι) →₀ ℕ) :
    ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
        (mvExp ((-S) • ∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) *
          MvPowerSeries.X (true, i)))‖ ≤ r ^ (∑ i, min (κ (false, i)) (κ (true, i))) := by
  classical
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hQ0 : MvPowerSeries.constantCoeff ((-S) • ∑ i, MvPowerSeries.C (u i) *
      MvPowerSeries.X (false, i) * MvPowerSeries.X (true, i) : MvPowerSeries (Bool × ι) K) = 0 := by
    simp
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hQ0
  unfold mvExp
  rw [PowerSeries.coeff_subst hs, mul_finsum]
  refine norm_finsum_le_of (pow_nonneg hr0 _) fun k => ?_
  rw [smul_pow, quad_pow, PowerSeries.coeff_exp, Finset.smul_sum, map_sum, Finset.smul_sum,
    Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun n hn => ?_
  rw [Finset.mem_piAntidiag] at hn
  have hk : ∑ i, n i = k := hn.1
  rw [← map_natCast (MvPowerSeries.C (σ := Bool × ι) (R := K)), ← MvPowerSeries.smul_eq_C_mul,
    map_smul, map_smul, MvPowerSeries.coeff_monomial]
  by_cases hκ : κ = pairExp n
  · rw [if_pos hκ]
    have hspec := Nat.multinomial_spec Finset.univ n
    rw [hk] at hspec
    have hk0 : ((k.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hval : ((mfact κ : ℕ) : K) * ((algebraMap ℚ K) (1 / (k.factorial : ℚ)) •
        ((-S) ^ k • ((Nat.multinomial Finset.univ n : ℕ) : K) • ∏ i, u i ^ n i)) =
        ((∏ i, (n i).factorial : ℕ) : K) * ((-S) ^ k * ∏ i, u i ^ n i) := by
      rw [hκ, mfact_pairExp, map_div₀, map_one, map_natCast, ← hspec]
      rw [← hspec] at hk0
      simp only [smul_eq_mul]
      push_cast at hk0 ⊢
      have hP := left_ne_zero_of_mul hk0
      have hM := right_ne_zero_of_mul hk0
      field_simp
    rw [hval, norm_mul, norm_mul, norm_pow, norm_neg, norm_prod]
    have h1 : ‖((∏ i, (n i).factorial : ℕ) : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K _
    have h2 : ∏ i, ‖u i ^ n i‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hu i)
    have h3 : ‖S‖ ^ k ≤ r ^ k := pow_le_pow_left₀ (norm_nonneg _) hS k
    have h4 : ∑ i, min (κ (false, i)) (κ (true, i)) = k := by
      rw [hκ, ← hk]
      simp only [pairExp_apply, min_self]
    rw [h4]
    calc ‖((∏ i, (n i).factorial : ℕ) : K)‖ * (‖S‖ ^ k * ∏ i, ‖u i ^ n i‖)
        ≤ 1 * (r ^ k * 1) := by
          apply mul_le_mul h1 _ (by positivity) zero_le_one
          exact mul_le_mul h3 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (pow_nonneg hr0 _)
      _ = r ^ k := by ring
  · rw [if_neg hκ]
    simp only [smul_zero, mul_zero, norm_zero]
    exact pow_nonneg hr0 _
end Formalism.DworkPowerSeriesWeights
