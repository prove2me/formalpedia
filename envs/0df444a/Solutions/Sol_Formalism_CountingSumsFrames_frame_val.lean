-- Prove2me | solution 1 for Formalism.CountingSumsFrames.frame_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:40:40.652992+00:00
-- url     : https://prove2.me/submissions/06173c6d-80a1-4077-b0f7-df5c13a0198f

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_fock_mult_val_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (p : ℕ) [Fact p.Prime] (D : ℕ) {r : ℕ} (m : Fin r → ℕ) (hm : ∑ i, m i ≤ D) :
    padicValNat p (D.choose (∑ i, m i) * Nat.multinomial univ m) ≤ (r + 1) * Nat.log p D := by
  have hc : D.choose (∑ i, m i) ≠ 0 := (Nat.choose_pos hm).ne'
  have hm0 : Nat.multinomial univ m ≠ 0 := (Nat.multinomial_pos _ _).ne'
  rw [padicValNat.mul hc hm0]
  have h1 : padicValNat p (D.choose (∑ i, m i)) ≤ Nat.log p D := by
    rw [← Nat.factorization_def _ (Fact.out : p.Prime)]
    exact Nat.factorization_choose_le_log
  have h2 := fock_mult_val_le p m univ
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h3 : Nat.log p (∑ i, m i) ≤ Nat.log p D := Nat.log_mono_right hm
  have h4 := Nat.mul_le_mul_left r h3
  rw [add_mul, one_mul]
  omega
end Formalism.CountingSumsFrames
