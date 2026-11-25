-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.hasWt_add_pow_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:59:44.506612+00:00
-- url     : https://prove2.me/submissions/dbb100dd-8ffe-45dc-bc22-9b2333d486b8

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_natCast_mul

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
theorem _root_.solution {l q : ℕ} (hv : v (l : k) = 1) (hq : 1 ≤ q)
    (hdiv : ∀ m, 0 < m → m < q → l ∣ q.choose m) (hw : wa ≤ wb)
    (ha : HasWt v r wa a) (hb : HasWt v r wb b) :
    HasWt v r (1 + ((q : ℝ) - 1) * wa + wb) ((a + b) ^ q - a ^ q - b ^ q) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have key : (a + b) ^ (p + 1) - a ^ (p + 1) - b ^ (p + 1)
      = ∑ m ∈ Finset.range p, ((p + 1).choose (m + 1) : MvPowerSeries Z k)
          * (a ^ (m + 1) * b ^ (p + 1 - (m + 1))) := by
    rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_zero,
      one_mul, Nat.choose_zero_right]
    rw [add_sub_cancel_right, add_sub_cancel_right]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [key]
  refine HasWt.sum _ fun m hm => ?_
  have hm' : m < p := Finset.mem_range.1 hm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hm'
  have h1 := ((ha.pow (m + 1)).mul (hb.pow (m + j + 1 + 1 - (m + 1)))).natCast_mul hv
    (hdiv (m + 1) (by omega) (by omega))
  refine h1.mono ?_
  have h2 : m + j + 1 + 1 - (m + 1) = j + 1 := by omega
  rw [h2]
  push_cast
  have : 0 ≤ (j : ℝ) * (wb - wa) := mul_nonneg (Nat.cast_nonneg j) (by linarith)
  nlinarith
end Formalism.BaseCaseIdentities
