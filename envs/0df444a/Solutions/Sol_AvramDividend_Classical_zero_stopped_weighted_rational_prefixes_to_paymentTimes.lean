-- Prove2me | solution 1 for AvramDividend.Classical.zero_stopped_weighted_rational_prefixes_to_paymentTimes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:52:06.927513+00:00
-- url     : https://prove2.me/submissions/5392d354-55b0-4f96-bf20-a39084411711

import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_rational_strict_prefix
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
import Theorems.Thm_AvramDividend_Classical_directed_stieltjes_prefixes_determine_union_reward
import Theorems.Thm_AvramDividend_Classical_zero_atom_free_stieltjes_reward_union
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (σ : ℝ≥0∞) (μ ν : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (hprefix : ∀ q : ℚ, 0 < (q : ℝ) →
      ENNReal.ofReal (q : ℝ) < σ →
      (∫⁻ t in Ioc (0 : ℝ) (q : ℝ), f t ∂μ) =
        (∫⁻ t in Ioc (0 : ℝ) (q : ℝ), f t ∂ν))
    (hzeroμ : μ {(0 : ℝ)} = 0) (hzeroν : ν {(0 : ℝ)} = 0)
    (hatomμ : ∀ T : ℝ, 0 < T → μ {T} = 0)
    (hatomν : ∀ T : ℝ, 0 < T → ν {T} = 0) :
    (∫⁻ t in paymentTimes σ, f t ∂μ) =
      (∫⁻ t in paymentTimes σ, f t ∂ν) := by
  by_cases hz : σ = 0
  · subst σ
    have hpay : paymentTimes (0 : ℝ≥0∞) = ({0} : Set ℝ) := by
      simpa using paymentTimes_min_zero_eq_singleton_zero (0 : ℝ≥0∞)
    rw [hpay]
    have hμ := zero_atom_free_stieltjes_reward_union μ f (∅ : Set ℝ) hzeroμ
    have hν := zero_atom_free_stieltjes_reward_union ν f (∅ : Set ℝ) hzeroν
    have hμzero : (∫⁻ t in ({0} : Set ℝ), f t ∂μ) = 0 := by
      simpa using hμ
    have hνzero : (∫⁻ t in ({0} : Set ℝ), f t ∂ν) = 0 := by
      simpa using hν
    rw [hμzero, hνzero]
  · have hpos : (0 : ℝ≥0∞) < σ := pos_iff_ne_zero.mpr hz
    let ι := {q : ℚ // 0 < (q : ℝ) ∧ ENNReal.ofReal (q : ℝ) < σ}
    let s : ι → Set ℝ := fun q => Ico (0 : ℝ) (q.val : ℝ)
    have hd : Directed (fun a b : Set ℝ => a ⊆ b) s := by
      intro a b
      rcases le_total (a.val : ℝ) (b.val : ℝ) with hab | hba
      · exact ⟨b, Set.Ico_subset_Ico_right hab, Subset.rfl⟩
      · exact ⟨a, Subset.rfl, Set.Ico_subset_Ico_right hba⟩
    have hp (q : ι) :
        (∫⁻ t in s q, f t ∂μ) = (∫⁻ t in s q, f t ∂ν) := by
      change (∫⁻ t in Ico (0 : ℝ) (q.val : ℝ), f t ∂μ) =
        (∫⁻ t in Ico (0 : ℝ) (q.val : ℝ), f t ∂ν)
      calc
        (∫⁻ t in Ico (0 : ℝ) (q.val : ℝ), f t ∂μ) =
          (∫⁻ t in Ioc (0 : ℝ) (q.val : ℝ), f t ∂μ) :=
            setLIntegral_congr (Ico_ae_eq_Ioc' hzeroμ (hatomμ _ q.prop.1))
        _ = (∫⁻ t in Ioc (0 : ℝ) (q.val : ℝ), f t ∂ν) :=
          hprefix q.val q.prop.1 q.prop.2
        _ = (∫⁻ t in Ico (0 : ℝ) (q.val : ℝ), f t ∂ν) :=
          (setLIntegral_congr
            (Ico_ae_eq_Ioc' hzeroν (hatomν _ q.prop.1))).symm
    have hUnion :
        (∫⁻ t in ⋃ q : ι, s q, f t ∂μ) =
          (∫⁻ t in ⋃ q : ι, s q, f t ∂ν) :=
      directed_stieltjes_prefixes_determine_union_reward μ ν f s hd hp
    have hpay : paymentTimes σ = ⋃ q : ι, s q := by
      simpa only [s, ι] using
        paymentTimes_eq_iUnion_rational_strict_prefix σ hpos
    rw [hpay]
    exact hUnion
