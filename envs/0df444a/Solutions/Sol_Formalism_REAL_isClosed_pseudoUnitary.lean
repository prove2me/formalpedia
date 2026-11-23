-- Prove2me | solution 1 for Formalism.REAL.isClosed_pseudoUnitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:59.086801+00:00
-- url     : https://prove2.me/submissions/a5f00484-646b-477c-9ae2-23fa70a1df8d

import Definitions.Def_Formalism_RealPlaceAnalysis_UJLocCompact
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInducingCoeMatrix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} := by
  show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Jm ε * g = Jm ε}
  exact isClosed_eq
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const
end Formalism.REAL
