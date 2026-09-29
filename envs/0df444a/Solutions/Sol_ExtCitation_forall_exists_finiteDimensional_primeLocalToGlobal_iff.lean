-- Prove2me | solution 1 for ExtCitation.forall_exists_finiteDimensional_primeLocalToGlobal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/232fe5b7-1246-5c5a-ad44-8f75ca8a07bc

import Definitions.Def_ExtEndgame_ProductionDatum
import Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_forall_exists_finiteDimensional_primeLocalToGlobal_iff

set_option autoImplicit false
open CategoryTheory ExtCitation
open Polynomial
open scoped Pointwise

theorem solution
    (q : Nat.Primes) [Fact (q : ℕ).Prime]
    {k : Type} [CommRing k] (M : Rep k (primeLocalGaloisGroup q)) :
    (∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m) ↔
      ∀ m : M, ∃ K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)), FiniteDimensional ℚ_[(q : ℕ)] K ∧
        ∀ s : primeLocalGaloisGroup q, s ∈ K.fixingSubgroup → M.ρ s m = m :=
  forall_congr' fun m =>
    exists_finiteDimensional_comap_localGaloisToGlobal_iff (q : ℕ)
      (fun U => ∀ s : primeLocalGaloisGroup q, s ∈ U → M.ρ s m = m)
      (fun _ _ hVU h s hs => h s (hVU hs))

end S_ExtCitation_forall_exists_finiteDimensional_primeLocalToGlobal_iff
end P2MW
export P2MW.S_ExtCitation_forall_exists_finiteDimensional_primeLocalToGlobal_iff (solution)
