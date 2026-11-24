-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.inverse_power_integral_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:37.427389+00:00
-- url     : https://prove2.me/submissions/bf104961-5ecf-4d6e-99a5-29a636ead1e6

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_integrable_radial_iff
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_integral_complex_radial_eq_two_pi_mul_integral_Ioi
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hasDerivAt_inv_one_add_sq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_tendsto_inv_one_add_sq_atTop

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.InversePowerIntegralPi := by
  have hnn : ∀ y ∈ Set.Ioi (0 : ℝ), 0 ≤ y * ((1 + y ^ 2) ^ 2)⁻¹ := fun y hy => by
    have : (0 : ℝ) < y := hy
    positivity
  constructor
  · rw [integrable_radial_iff (fun y => ((1 + y ^ 2) ^ 2)⁻¹)]
    exact integrableOn_Ioi_deriv_of_nonneg' (fun y _ => hasDerivAt_inv_one_add_sq y) hnn tendsto_inv_one_add_sq_atTop
  · rw [integral_complex_radial_eq_two_pi_mul_integral_Ioi (fun y => ((1 + y ^ 2) ^ 2)⁻¹),
      integral_Ioi_of_hasDerivAt_of_nonneg' (fun y _ => hasDerivAt_inv_one_add_sq y) hnn tendsto_inv_one_add_sq_atTop]
    ring
end Formalism.HermitianLatticeCounting.P
