-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.signed_minor_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:35.921961+00:00
-- url     : https://prove2.me/submissions/30cea760-f31f-4b52-9079-c7cd827f1c64

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {F : Type} [Field F] {p : ℕ} (s : Fin p → ℕ) (t : Fin p → F) (a : Fin p) :
    IndexedMinorEntry s t a = (∏ a' ∈ univ.filter (fun a' : Fin p => a' < a), ((ParitySign (s a') : ℤ) : F) * t a' ^ s a') *
      (((ParitySign (s a) : ℤ) : F) * t a ^ s a) := by
  have h : univ.filter (fun a' : Fin p => a' ≤ a) = insert a (univ.filter (fun a' : Fin p => a' < a)) := by
    ext x
    simp [le_iff_lt_or_eq, or_comm]
  unfold IndexedMinorEntry
  rw [h, Finset.prod_insert (by simp), mul_comm]
end Formalism.HermitianLatticeCounting.P
