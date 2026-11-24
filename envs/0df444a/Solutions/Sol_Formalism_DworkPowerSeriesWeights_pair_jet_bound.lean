-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.pair_jet_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:19:21.122738+00:00
-- url     : https://prove2.me/submissions/2853f5c3-f7f2-4851-bcb3-b93bf13cb3ca

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_mul_dvd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_exp_jet
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : PairJet.{u} := by
  intro K _ _ _ pi h0 h1 ι _ S u hS hu sg hsg κ
  classical
  set r : ℝ := pi ^ (-(1 / 2 : ℝ)) with hrdef
  have hr : 1 ≤ r := Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1.le (by norm_num)
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hrhs : pi ^ (-(1 / 2 : ℝ) * ∑ i, (min (κ (false, i)) (κ (true, i)) : ℝ)) =
      r ^ (∑ i, min (κ (false, i)) (κ (true, i))) := by
    rw [Real.rpow_mul h0.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    rfl
  rw [hrhs, MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  obtain ⟨c, hc⟩ := mfact_mul_dvd p.1 p.2
  rw [hp] at hc
  have hE := exp_jet r hr ι S u hS hu p.1
  have hG := hsg p.2
  have hcn : ‖((c : ℕ) : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K _
  set E := mvExp ((-S) • ∑ i, MvPowerSeries.C (u i) * MvPowerSeries.X (false, i) *
          MvPowerSeries.X (true, i) : MvPowerSeries (Bool × ι) K)
  have hre : ((mfact κ : ℕ) : K) * (MvPowerSeries.coeff p.1 E * MvPowerSeries.coeff p.2 sg) =
      (((mfact p.1 : ℕ) : K) * MvPowerSeries.coeff p.1 E) *
        ((((mfact p.2 : ℕ) : K) * MvPowerSeries.coeff p.2 sg) * ((c : ℕ) : K)) := by
    rw [hc]; push_cast; ring
  rw [hre, norm_mul, norm_mul (((mfact p.2 : ℕ) : K) * MvPowerSeries.coeff p.2 sg)]
  have hmono : r ^ (∑ i, min (p.1 (false, i)) (p.1 (true, i))) ≤
      r ^ (∑ i, min (κ (false, i)) (κ (true, i))) := by
    apply pow_le_pow_right₀ hr
    apply Finset.sum_le_sum fun i _ => ?_
    rw [← hp]
    simp only [Finsupp.add_apply]
    omega
  calc _ ≤ r ^ (∑ i, min (p.1 (false, i)) (p.1 (true, i))) * (1 * 1) := by
        apply mul_le_mul hE _ (by positivity) (pow_nonneg hr0 _)
        exact mul_le_mul hG hcn (norm_nonneg _) zero_le_one
    _ ≤ _ := by rw [mul_one, mul_one]; exact hmono
end Formalism.DworkPowerSeriesWeights
