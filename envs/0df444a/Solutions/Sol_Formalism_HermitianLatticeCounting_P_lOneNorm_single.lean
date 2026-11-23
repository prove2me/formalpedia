-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.lOneNorm_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:08.69013+00:00
-- url     : https://prove2.me/submissions/d25f2aa9-157f-4aa5-b4df-2975dfbca333

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
theorem _root_.solution {P : Type} (p : P) (c : ℂ) : lOneNorm (Finsupp.single p c) = ‖c‖ := by
  simp [lOneNorm]
end Formalism.HermitianLatticeCounting.P
