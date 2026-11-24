-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.gcd_mul_pow_totient
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:36.463251+00:00
-- url     : https://prove2.me/submissions/2c83a486-7c66-4864-97fe-e521e9cc2d73

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {q m : ℕ} (hm : 0 < m) (hcop : Nat.Coprime q m) :
    Nat.gcd (q * m) (q ^ Nat.totient m) = q := by
  have ht : 0 < Nat.totient m := Nat.totient_pos.mpr hm
  obtain ⟨k, hk⟩ : ∃ k, Nat.totient m = k + 1 := ⟨Nat.totient m - 1, by omega⟩
  rw [hk, pow_succ', Nat.gcd_mul_left]
  have : Nat.gcd m (q ^ k) = 1 := (Nat.Coprime.pow_right k hcop.symm)
  rw [this, mul_one]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
