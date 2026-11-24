-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gl_radial_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:27.476263+00:00
-- url     : https://prove2.me/submissions/f4496bb8-d92e-46ed-922b-459fc7bfdc8a

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (f : ℝ → ℝ) :
    Integrable (fun x : ℂ => f ‖x‖) ↔ IntegrableOn (fun y : ℝ => y * f y) (Set.Ioi 0) := by
  have h := integrable_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ) (f := f)
  simpa [Complex.finrank_real_complex] using h
end Formalism.HermitianLatticeCounting.P
