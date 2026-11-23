-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gh_det_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:44.778424+00:00
-- url     : https://prove2.me/submissions/23db0439-59fb-4610-b6d7-39139405d59e

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
variable {n β K : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] [LinearOrder β] [Field K]
  {b : n → β} {σ : n → n}
omit [LinearOrder β]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {u : Matrix n n K} (h1 : ∀ i, u i i = 1) (h2 : ∀ i j, j < i → u i j = 0) :
    u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h2 i j hij)]
  simp [h1]
end Formalism.HermitianLatticeCounting.P
