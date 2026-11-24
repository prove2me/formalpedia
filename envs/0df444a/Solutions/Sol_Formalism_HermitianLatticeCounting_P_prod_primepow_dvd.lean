-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prod_primepow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:47.427569+00:00
-- url     : https://prove2.me/submissions/e22edc2d-a935-4887-be5d-44c0ca10bb1a

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (e : ℕ → ℕ) (n : ℕ)
    (h : ∀ p ∈ s, p ^ e p ∣ n) : ∏ p ∈ s, p ^ e p ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.prod_insert hp]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ (h p (Finset.mem_insert_self _ _))
      (ih (fun q hq => hs q (Finset.mem_insert_of_mem hq)) (fun q hq => h q (Finset.mem_insert_of_mem hq)))
    apply Nat.Coprime.prod_right
    intro q hq
    apply Nat.Coprime.pow
    exact (Nat.coprime_primes (hs p (Finset.mem_insert_self _ _)) (hs q (Finset.mem_insert_of_mem hq))).2
      (fun hpq => hp (hpq ▸ hq))
end Formalism.HermitianLatticeCounting.P
