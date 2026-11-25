-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.frob_sum_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:40:58.173251+00:00
-- url     : https://prove2.me/submissions/b25a30a5-ebec-425d-a25c-25fd7b72d82a

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Theorems.Thm_Formalism_BaseCaseIdentities_coeff_sum_C_mul_X_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
variable {k : Type*} [Field k] {Z : Type*} {v : AddValuation k (WithTop ℝ)}
  {r w w' w1 w2 wa wb a₀ : ℝ} {f g a b : MvPowerSeries Z k}
namespace Formalism.BaseCaseIdentities
theorem _root_.solution [Fintype Z] {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (x : Z → k) :
    frob N (∑ d, C (x d) * X d ^ M) = ∑ d, C (x d ^ N) * X d ^ (N * M) := by
  classical
  ext B
  rw [coeff_sum_C_mul_X_pow]
  by_cases hB : ∃ d0, B = Finsupp.single d0 (N * M)
  · obtain ⟨d0, rfl⟩ := hB
    have h1 : ∀ d, N ∣ (Finsupp.single d0 (N * M)) d := by
      intro d
      by_cases h : d0 = d
      · subst h; simp
      · simp [h]
    have h2 : (Finsupp.single d0 (N * M)).mapRange (· / N) (Nat.zero_div N)
        = Finsupp.single d0 M := by
      rw [Finsupp.mapRange_single]
      congr 1
      exact Nat.mul_div_cancel_left M (by omega)
    rw [coeff_frob_of_dvd h1, h2, coeff_sum_C_mul_X_pow]
    have hNM : N * M ≠ 0 := by positivity
    have hM0 : M ≠ 0 := by omega
    simp only [Finsupp.single_left_inj hNM, Finsupp.single_left_inj hM0]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp
  · have hR : ∀ d, B ≠ Finsupp.single d (N * M) := fun d h => hB ⟨d, h⟩
    rw [Finset.sum_eq_zero (fun d _ => if_neg (hR d))]
    by_cases h : ∀ d, N ∣ B d
    · rw [coeff_frob_of_dvd h, coeff_sum_C_mul_X_pow]
      have hL : ∀ d, B.mapRange (· / N) (Nat.zero_div N) ≠ Finsupp.single d M := by
        intro d hd
        apply hR d
        rw [← smul_mapRange_div h, hd, Finsupp.smul_single, smul_eq_mul]
      rw [Finset.sum_eq_zero (fun d _ => if_neg (hL d))]
      exact zero_pow (by omega)
    · rw [coeff_frob_of_not_dvd h]
end Formalism.BaseCaseIdentities
