-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gram_majorant_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:54.418563+00:00
-- url     : https://prove2.me/submissions/24dac4bd-698c-4e9d-88fc-4ac254066822

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gb_norm_theta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset
open scoped ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.MajorantNormBound := by
  intro V _ _ θ hθ x
  unfold majorantHermitianForm
  calc ‖inner ℂ (θ x) x‖ ≤ ‖θ x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ = ‖x‖ ^ 2 := by rw [gb_norm_theta hθ, sq]
end Formalism.HermitianLatticeCounting.P
