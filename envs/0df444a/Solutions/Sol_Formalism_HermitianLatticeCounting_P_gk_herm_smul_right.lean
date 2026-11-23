-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gk_herm_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:45.453659+00:00
-- url     : https://prove2.me/submissions/6c1bd6f2-aca1-40f0-8fc0-b709dfa9a0ef

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
    herm H u (c • w) = star c * herm H u w := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]
end Formalism.HermitianLatticeCounting.P
