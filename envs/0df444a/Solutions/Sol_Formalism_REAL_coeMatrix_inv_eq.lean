-- Prove2me | solution 1 for Formalism.REAL.coeMatrix_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:18.260846+00:00
-- url     : https://prove2.me/submissions/765ec8f7-a3b2-4147-b18d-f0644ddad93b

import Definitions.Def_Formalism_RealPlaceAnalysis_UJLocCompact
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInducingCoeMatrix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Theorems.Thm_Formalism_REAL_coeMatrix_left_inv

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) :
    (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = Jm ε * (coeMatrixAlt ε g)ᴴ * Jm ε :=
  Units.inv_eq_of_mul_eq_one_left (coeMatrix_left_inv ε _ g.2)
end Formalism.REAL
