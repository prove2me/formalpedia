-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.discr_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:15:53.448153+00:00
-- url     : https://prove2.me/submissions/2f91eae5-36be-4c22-af87-ec8700f9c2f6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_DiscrMulIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open NumberField Matrix
namespace Formalism.L2.Pj.FundamentalDomainD5
theorem _root_.solution {K : Type} [Field K] [NumberField K] (z : K)
    (hz : ∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (z * a) = n) :
    IsIntegral ℤ ((NumberField.discr K : K) * z) := by
  classical
  have hne : (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K))

  have hz1 : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have h1ne : (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := by
      rw [← FractionalIdeal.coeIdeal_top]
      exact FractionalIdeal.coeIdeal_ne_zero.mpr top_ne_bot
    rw [FractionalIdeal.mem_dual h1ne]
    intro a ha
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨n, hn⟩ := hz a'
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hn.symm

  set N : ℕ := Ideal.absNorm (differentIdeal ℤ (𝓞 K)) with hN
  have hNmem : (N : K) ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨(N : 𝓞 K), Ideal.absNorm_mem _, by simp⟩
  have hprod : z * (N : K) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have h := FractionalIdeal.mul_mem_mul hz1 hNmem
    have hdual : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹ := by
      rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]
    rwa [hdual, inv_mul_cancel₀ hne] at h
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).mp hprod
  have hint : IsIntegral ℤ (z * (N : K)) := by
    rw [← hx]; exact RingOfIntegers.isIntegral_coe x
  have hNd : N = (NumberField.discr K).natAbs := NumberField.absNorm_differentIdeal K (𝓞 K)
  rcases Int.natAbs_eq (NumberField.discr K) with h | h
  · rw [h, ← hNd, Int.cast_natCast, mul_comm]; exact hint
  · rw [h, ← hNd, Int.cast_neg, Int.cast_natCast, neg_mul, mul_comm]; exact hint.neg
end Formalism.L2.Pj.FundamentalDomainD5
