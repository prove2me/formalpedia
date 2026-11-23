-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:39:45.528448+00:00
-- url     : https://prove2.me/submissions/e7a8c929-948e-4194-ab99-12878183ab97

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
section SlopeTestRemainingChoices
variable {K : Type} [Field K] [NumberField K] [StarRing K]
private theorem vw_coe_eq_count_factors_span_of_ne_zero (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    vw w (x : K) = ((Associates.mk w.asIdeal).count
      (Associates.mk (Ideal.span {x} : Ideal (𝓞 K))).factors : ℤ) := by
  have hspan : (Ideal.span {x} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold vw
  rw [← FractionalIdeal.count_coe K w hspan, FractionalIdeal.coeIdeal_span_singleton]
end SlopeTestRemainingChoices
end Formalism.EigenvalueLevelCeiling
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (hn : n ≠ 0) :
    ∑ w ∈ T, lw w * (vw w (n : K) : ℝ) ≤ Real.log (n : ℝ) := by
  classical
  have hd0 : (0 : ℝ) < (finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hn0 : ((n : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hn
  have hI0 : (Ideal.span {((n : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hn0

  obtain ⟨e, he⟩ : ∃ e : HeightOneSpectrum (𝓞 K) → ℕ, ∀ w, e w =
      (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {((n : ℕ) : 𝓞 K)})).factors :=
    ⟨_, fun _ => rfl⟩
  have hv : ∀ w, vw w (n : K) = (e w : ℤ) := by
    intro w
    have h := vw_coe_eq_count_factors_span_of_ne_zero w _ hn0
    rw [he w]
    have hc : (((n : ℕ) : 𝓞 K) : K) = (n : K) := by
      first
        | (push_cast; rfl)
        | push_cast
        | simp
    rw [hc] at h
    exact h

  have hdiv : ∀ w : HeightOneSpectrum (𝓞 K),
      w.asIdeal ^ e w ∣ Ideal.span {((n : ℕ) : 𝓞 K)} := by
    intro w
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem,
      ← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem,
      IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg w hn0, he w]
  have hdvd : ∏ w ∈ T, w.asIdeal ^ e w ∣ Ideal.span {((n : ℕ) : 𝓞 K)} := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      show IsCoprime (a.asIdeal ^ e a) (b.asIdeal ^ e b)
      apply IsCoprime.pow
      rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne a.isMaximal b.isMaximal
        (fun h => hab (HeightOneSpectrum.ext h))
    · intro w _
      exact hdiv w
  have hP0 : Ideal.absNorm (∏ w ∈ T, w.asIdeal ^ e w) ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]
    intro h
    rw [h, zero_dvd_iff] at hdvd
    exact hI0 hdvd
  have hle : Ideal.absNorm (∏ w ∈ T, w.asIdeal ^ e w) ≤
      Ideal.absNorm (Ideal.span {((n : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) := by
    apply Nat.le_of_dvd
    · apply Nat.pos_of_ne_zero
      rw [ne_eq, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]
      exact hI0
    · exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
  have hnormI : Ideal.absNorm (Ideal.span {((n : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) =
      n ^ finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 K)) n,
      Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have hNw : ∀ w : HeightOneSpectrum (𝓞 K), (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
    intro w
    have : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    exact_mod_cast this
  have hlog : Real.log (Ideal.absNorm (∏ w ∈ T, w.asIdeal ^ e w) : ℝ) =
      ∑ w ∈ T, (e w : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) := by
    rw [map_prod, Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [map_pow, Nat.cast_pow, Real.log_pow]
    · intro w _
      rw [map_pow, Nat.cast_pow]
      exact pow_ne_zero _ (hNw w)
  have hlogle : ∑ w ∈ T, (e w : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) ≤
      (finrank ℚ K : ℝ) * Real.log (n : ℝ) := by
    rw [← hlog, ← Real.log_pow, ← Nat.cast_pow, ← hnormI]
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero hP0
    · exact_mod_cast hle
  have hsum : ∑ w ∈ T, lw w * (vw w (n : K) : ℝ) =
      (∑ w ∈ T, (e w : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ)) / (finrank ℚ K : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hv w]
    unfold lw
    push_cast
    ring
  rw [hsum, div_le_iff₀ hd0, mul_comm (Real.log (n : ℝ))]
  exact hlogle
end Formalism.EigenvalueLevelCeiling
