-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gk_herm_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:30:11.279716+00:00
-- url     : https://prove2.me/submissions/6c48ff64-398e-4ffc-a213-3a0ebd20fc2e

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
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants Matrix
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (u w : ι → ℂ) :
    herm H (c • u) w = c * herm H u w := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
end Formalism.HermitianLatticeCounting.P
