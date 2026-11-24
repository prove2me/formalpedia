-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.eq_one_of_sub_one_mem_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:29.390994+00:00
-- url     : https://prove2.me/submissions/5fa70484-70eb-4cb4-a8eb-0f1ca4a028bb

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_ProdInfinitePlaceLeOfIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
namespace Formalism.SLP.GlobalBoundRefinements.P
theorem _root_.solution : Formalism.SLP.GlobalBoundRefinements.RootUnityTriv := by
  intro E _ _ α P hP hw h1 hm

  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ
    (NumberField.RingOfIntegers.isIntegral_coe α) (fun φ => by
      have := hw (NumberField.InfinitePlace.mk φ)
      rwa [NumberField.InfinitePlace.apply] at this)
  have hpowO : α ^ n = 1 := NumberField.RingOfIntegers.ext (by simpa using hpow)
  have hu : Units.ofPowEqOne α n hpowO hn.ne' ∈ NumberField.Units.torsion E := by
    rw [NumberField.Units.mem_torsion]
    intro w
    simpa using hw w
  have hm1 : α ^ Nat.card (NumberField.Units.torsion E) = 1 := by
    have := congrArg (fun g : NumberField.Units.torsion E => (((g : (RingOfIntegers E)ˣ)) : RingOfIntegers E))
      (pow_card_eq_one' (x := (⟨_, hu⟩ : NumberField.Units.torsion E)))
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Units.val_ofPowEqOne,
      OneMemClass.coe_one, Units.val_one] at this
    exact this
  by_contra hne
  apply hm

  have hsum : ∑ i ∈ Finset.range (Nat.card (NumberField.Units.torsion E)), α ^ i = 0 := by
    have h := geom_sum_mul α (Nat.card (NumberField.Units.torsion E))
    rw [hm1, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  have hdiff : ∑ i ∈ Finset.range (Nat.card (NumberField.Units.torsion E)), (α ^ i - 1) ∈ P := by
    refine Ideal.sum_mem _ (fun i _ => ?_)
    obtain ⟨c, hc⟩ : α - 1 ∣ α ^ i - 1 := by simpa using sub_dvd_pow_sub_pow α 1 i
    rw [hc]
    exact P.mul_mem_right c h1
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    zero_sub, neg_mem_iff] at hdiff
  exact hdiff
end Formalism.SLP.GlobalBoundRefinements.P
