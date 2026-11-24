-- Prove2me | solution 1 for Formalism.SLP.P.card_submodules_of_index_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:34:31.099491+00:00
-- url     : https://prove2.me/submissions/35ecb2c2-78ab-4c64-9945-7490bc000a7d

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
import Theorems.Thm_Formalism_SLP_P_CountO_mul_count
import Theorems.Thm_Formalism_SLP_P_CountO_count_prime_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open CountO
namespace Formalism.SLP.P
theorem _root_.solution : Formalism.SLP.SubmoduleIndexCountO := by
  intro E _ _ M _ _ _ _ j hj
  set k := finrank (𝓞 E) M
  have htf : TF E M := fun a ha x hx => by
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := M)
      (mem_nonZeroDivisors_of_ne_zero ha)
    exact h (hx.trans (smul_zero a).symm)
  have hli : LIB E M k := fun ι _ v hv => hv.fintype_card_le_finrank
  have key : ∀ j : ℕ, 1 ≤ j → (idxSet (𝓞 E) M j).Finite ∧
      (idxSet (𝓞 E) M j).ncard ≤
        finrank ℚ E ^ (Nat.primeFactorsList j).length * j ^ k := by
    intro j
    induction j using Nat.recOnPosPrimePosCoprime with
    | prime_pow p e hp _ =>
      intro _
      have h := count_prime_pow k p hp e M htf hli
      rw [hp.primeFactorsList_pow, List.length_replicate]
      exact h
    | zero => intro h; omega
    | one =>
      intro _
      have h := count_prime_pow k 2 Nat.prime_two 0 M htf hli
      simpa using h
    | coprime a b ha hb hab iha ihb =>
      intro _
      obtain ⟨fa, ca⟩ := iha (by omega)
      obtain ⟨fb, cb⟩ := ihb (by omega)
      obtain ⟨fab, cab⟩ := mul_count hab (by omega) (by omega) fa fb
      refine ⟨fab, cab.trans ?_⟩
      rw [(Nat.perm_primeFactorsList_mul (by omega) (by omega)).length_eq, List.length_append,
        pow_add, mul_pow]
      calc (idxSet (𝓞 E) M a).ncard * (idxSet (𝓞 E) M b).ncard
          ≤ (finrank ℚ E ^ (Nat.primeFactorsList a).length * a ^ k) *
            (finrank ℚ E ^ (Nat.primeFactorsList b).length * b ^ k) := Nat.mul_le_mul ca cb
        _ = _ := by ring
  exact key j hj
end Formalism.SLP.P
