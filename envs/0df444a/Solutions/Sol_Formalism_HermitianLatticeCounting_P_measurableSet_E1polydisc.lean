-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.measurableSet_E1polydisc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:38.521992+00:00
-- url     : https://prove2.me/submissions/79cff63a-4748-41fe-9d1f-d54411dd4dbb

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_polydisc_eq_pi_ball

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
theorem _root_.solution {ι : Type} [Fintype ι] (ro : ℝ) (D : ι → ℂ) : MeasurableSet (CenteredPolydisc ro D) := by
  rw [polydisc_eq_pi_ball]
  exact MeasurableSet.univ_pi fun v => measurableSet_ball
end Formalism.HermitianLatticeCounting.P
