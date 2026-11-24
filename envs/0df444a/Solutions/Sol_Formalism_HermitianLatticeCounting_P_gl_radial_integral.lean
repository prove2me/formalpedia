-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gl_radial_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:14.780805+00:00
-- url     : https://prove2.me/submissions/6cdb008d-17c2-468e-9d77-d48e994d93eb

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
    ∫ x : ℂ, f ‖x‖ = 2 * π * ∫ y in Set.Ioi (0 : ℝ), y * f y := by
  have h := integral_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ) f
  have hv : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    simp [Measure.real, Complex.volume_ball]
  rw [h, hv]
  simp [Complex.finrank_real_complex]
  ring
end Formalism.HermitianLatticeCounting.P
