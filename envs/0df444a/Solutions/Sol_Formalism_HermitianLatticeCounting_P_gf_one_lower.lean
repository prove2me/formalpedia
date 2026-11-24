-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gf_one_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:24.695445+00:00
-- url     : https://prove2.me/submissions/f542c6b5-9261-4c37-a935-978c4f73d8c6

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
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R : Type*} [CommRing R] {d : ℕ} : IsLowerUnitriangular (1 : Matrix (Fin d) (Fin d) R) := by
  unfold IsLowerUnitriangular
  exact ⟨fun i => Matrix.one_apply_eq i, fun i j h => Matrix.one_apply_ne (ne_of_lt h)⟩
end Formalism.HermitianLatticeCounting.P
