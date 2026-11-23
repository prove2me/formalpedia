-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gk_herm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:44.780993+00:00
-- url     : https://prove2.me/submissions/f5d3422e-55e3-4323-b734-cb210a920d28

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
theorem _root_.solution {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (u v w : ι → ℂ) :
    herm H u (v + w) = herm H u v + herm H u w := by
  simp only [herm, star_add, add_dotProduct]
end Formalism.HermitianLatticeCounting.P
