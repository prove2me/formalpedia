-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.zf_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:21.721331+00:00
-- url     : https://prove2.me/submissions/c5c0f9a2-4675-4ff8-a9b3-9be4041741ee

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution {f : Fn r} (z : ℂ) (hf : ZF f) : ZF (z • f) := fun l =>
  ⟨by rw [map_smul, (hf l).1, smul_zero], by rw [map_smul, (hf l).2, smul_zero]⟩
end Formalism.FourierDecayAlt.P.Mx2
