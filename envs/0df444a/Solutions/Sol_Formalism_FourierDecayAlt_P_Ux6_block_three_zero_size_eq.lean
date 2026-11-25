-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.block_three_zero_size_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:02:14.040996+00:00
-- url     : https://prove2.me/submissions/0bfa8100-a9dc-48d0-aa30-57b08933a348

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_block3_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_ext_eB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution : blk3 (k := k) (j := j) (ρ := ρ) 0 0 0 0 0 0 0 0 0 = 0 := by
  apply ext_eB
  rintro (((a | a) | a)) (((b | b) | b)) <;> simp [block3_apply]
end Formalism.FourierDecayAlt.P.Ux6
