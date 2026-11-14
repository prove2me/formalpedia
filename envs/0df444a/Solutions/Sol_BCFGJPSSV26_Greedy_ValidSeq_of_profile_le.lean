-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.ValidSeq.of_profile_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:58:06.882925+00:00
-- url     : https://prove2.me/submissions/78e48c7d-3679-4162-92db-b69c45c536b0

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Openable
public import Definitions.Def_BCFGJPSSV26_Greedy_Valid
import all Definitions.Def_BCFGJPSSV26_Greedy_Valid
public import Theorems.Thm_BCFGJPSSV26_Greedy_maximal_transfer

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

variable {P d}

/-- A sequence of valid atoms whose profile is below that of a maximal sequence is maximal,
without overbidding. -/
theorem ValidSeq.of_profile_le (hP : P.Good n) (hd0 : ∀ j i, 0 ≤ d j i) {f η : ℚ} {p : ℕ}
    {pre pre' H H' : List (Atom m)} (hv : ValidSeq P d f η p pre H)
    (hno : NoOver P d f (P.θseq p) (profL P.K d (pre ++ H)))
    (hat : ∀ t (ht : t < H'.length), ValidAt P d f η p (pre' ++ H'.take t) H'[t])
    (hle : profL P.K d (pre' ++ H') ≤ profL P.K d (pre ++ H)) : ValidSeq P d f η p pre' H' :=
  ⟨hat, maximal_transfer hP hd0 (typ1 p) (θseq_pos P p) hno hle le_rfl hv.2⟩

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.ValidSeq.of_profile_le := @BCFGJPSSV26.Greedy.ValidSeq.of_profile_le
