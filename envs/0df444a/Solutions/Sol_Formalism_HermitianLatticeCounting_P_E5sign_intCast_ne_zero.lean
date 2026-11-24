-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.E5sign_intCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:16.111806+00:00
-- url     : https://prove2.me/submissions/4f7ec80e-6d28-48bd-993a-654b50b8781a

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
theorem _root_.solution {F : Type} [Field F] (k : ℕ) : ((ParitySign k : ℤ) : F) ≠ 0 := by
  unfold ParitySign
  push_cast
  exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
end Formalism.HermitianLatticeCounting.P
