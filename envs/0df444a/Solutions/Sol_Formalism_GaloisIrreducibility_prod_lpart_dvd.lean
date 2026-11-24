-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.prod_lpart_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:12.302861+00:00
-- url     : https://prove2.me/submissions/2d847201-c4dc-4c29-a8b0-64482c4a1b08

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_FewLargeParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Finset
namespace Formalism.GaloisIrreducibility
theorem _root_.solution (n : ℕ) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    (∏ l ∈ S, l ^ padicValNat l n) ∣ n := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert l S hl ih =>
    rw [Finset.prod_insert hl]
    have hlp : l.Prime := hS l (Finset.mem_insert_self l S)
    have ih' := ih (fun l' hl' => hS l' (Finset.mem_insert_of_mem hl'))
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · apply Nat.Coprime.prod_right
      intro l' hl'
      have hl'p : l'.Prime := hS l' (Finset.mem_insert_of_mem hl')
      apply Nat.Coprime.pow
      exact (Nat.coprime_primes hlp hl'p).2 (fun h => hl (h ▸ hl'))
    · exact pow_padicValNat_dvd
    · exact ih'
end Formalism.GaloisIrreducibility
