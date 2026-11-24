-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.multinomial_fact_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:08:31.677592+00:00
-- url     : https://prove2.me/submissions/2830b570-1783-4ed6-9cd3-4f0c41b7bc0a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
variable {v} {p : ℕ} [CharZero K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {ι : Type*} (q : ℕ) (f : ι → ℕ) (s : Finset ι) :
    (Nat.multinomial s f).factorization q ≤ s.card * Nat.log q (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Nat.multinomial_insert ha,
      Nat.factorization_mul (Nat.choose_pos (by omega)).ne' (Nat.multinomial_pos _ _).ne',
      Finsupp.add_apply, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    have h1 := @Nat.factorization_choose_le_log q (f a + ∑ i ∈ s, f i) (f a)
    have h2 : Nat.log q (∑ i ∈ s, f i) ≤ Nat.log q (f a + ∑ i ∈ s, f i) :=
      Nat.log_mono_right (by omega)
    calc _ ≤ Nat.log q (f a + ∑ i ∈ s, f i) + s.card * Nat.log q (∑ i ∈ s, f i) := add_le_add h1 ih
      _ ≤ Nat.log q (f a + ∑ i ∈ s, f i) + s.card * Nat.log q (f a + ∑ i ∈ s, f i) := by gcongr
      _ = (s.card + 1) * Nat.log q (f a + ∑ i ∈ s, f i) := by ring
end Formalism.MainNotions.PlaneGram
