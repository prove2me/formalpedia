-- Prove2me | solution 2 for Formalism.HermitianLatticeCounting.P.foldr_ofFn_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:42.677642+00:00
-- url     : https://prove2.me/submissions/72ed61e0-51c6-4e7d-8f1b-c65337320858

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
theorem _root_.solution {W ι : Type} (Eop : ι → W → W) (q : ℕ) (i : ι) (τ : Fin q → ι) (w : W) :
    (List.ofFn (Fin.cons i τ : Fin (q + 1) → ι)).foldr Eop w = Eop i ((List.ofFn τ).foldr Eop w) := by
  simp [List.ofFn_succ]
end Formalism.HermitianLatticeCounting.P
