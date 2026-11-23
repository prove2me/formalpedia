-- Prove2me | solution 1 for Formalism.REAL.range_coeMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:46.069795+00:00
-- url     : https://prove2.me/submissions/9c54bc7c-293c-4aad-bebf-9269988a9964

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) :
    Set.range (coeMatrixAlt ε) = {g | inUJ ε g} := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact u.2
  · intro hg
    have hl := coeMatrix_left_inv ε g hg
    let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨g, Jm ε * gᴴ * Jm ε, mul_eq_one_comm.mp hl, hl⟩
    exact ⟨⟨u, hg⟩, rfl⟩
end Formalism.REAL
