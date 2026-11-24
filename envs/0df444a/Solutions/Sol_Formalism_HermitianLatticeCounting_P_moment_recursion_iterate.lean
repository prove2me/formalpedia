-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.moment_recursion_iterate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:41.86334+00:00
-- url     : https://prove2.me/submissions/ae034aa0-63e1-48fa-9829-7057d71901aa

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentRecursionIterate := by
  intro P ι step d MM c q0 J hd h0 hs q
  induction q with
  | zero => intro μ j _ _; simpa using h0 μ j
  | succ q ih =>
    intro μ j h1 h2
    calc MM (q+1) μ j ≤ c * ⨆ s, MM q (step μ s) (j+2) := hs q μ j (by omega) (by omega)
      _ ≤ c * c^q := by
          gcongr
          exact iSup_le fun s => ih _ _ (by have := hd μ s; omega) (by omega)
      _ = c^(q+1) := by rw [pow_succ, mul_comm]
end Formalism.HermitianLatticeCounting.P
