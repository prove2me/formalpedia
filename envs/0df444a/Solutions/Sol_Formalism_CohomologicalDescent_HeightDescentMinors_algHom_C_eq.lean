-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.algHom_C_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:23.792817+00:00
-- url     : https://prove2.me/submissions/c024e176-7e8f-44e1-b60a-9493c149d9d4

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution {R : Type} [CommRing R] (Φ : R⟦X⟧ →ₐ[R] R⟦X⟧) (a : R) : Φ (C a) = C a := by
  calc Φ (C a) = Φ (a • 1) := by rw [PowerSeries.smul_eq_C_mul, mul_one]
    _ = a • Φ 1 := map_smul Φ a 1
    _ = C a := by rw [map_one, PowerSeries.smul_eq_C_mul, mul_one]
end Formalism.CohomologicalDescent.HeightDescentMinors
