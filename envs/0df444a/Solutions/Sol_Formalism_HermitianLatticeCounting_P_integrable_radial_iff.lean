-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integrable_radial_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:08.183056+00:00
-- url     : https://prove2.me/submissions/aa4512e8-b171-423e-83ff-6e2b9216067f

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
theorem _root_.solution (f : ℝ → ℝ) :
    Integrable (fun x : ℂ => f ‖x‖) ↔ IntegrableOn (fun y : ℝ => y * f y) (Set.Ioi 0) := by
  have h := integrable_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ) (f := f)
  simpa [Complex.finrank_real_complex] using h
end Formalism.HermitianLatticeCounting.P
