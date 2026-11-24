-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.foldr_mem_filtration
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:47.502018+00:00
-- url     : https://prove2.me/submissions/82a2f443-afd2-4c65-ac5a-6d1bf2876607

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
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {W ι : Type} (Eop : ι → W → W) (Fil : ℕ → Set W)
    (hF : ∀ i j w, w ∈ Fil j → Eop i w ∈ Fil (j + 2)) (j : ℕ) (w : W) (hw : w ∈ Fil j) (l : List ι) :
    l.foldr Eop w ∈ Fil (j + 2 * l.length) := by
  induction l with
  | nil => simpa using hw
  | cons i l ih =>
    have := hF i _ _ ih
    simpa [List.foldr_cons, List.length_cons, mul_add, add_assoc] using this
end Formalism.HermitianLatticeCounting.P
