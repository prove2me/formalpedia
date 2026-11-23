-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.upperUni_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:33.186136+00:00
-- url     : https://prove2.me/submissions/4c9185bf-868f-4641-8679-7334086e21db

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution {d : ℕ} : IsUpperUni (1 : Matrix (Fin d) (Fin d) ℂ) :=
  ⟨fun i => Matrix.one_apply_eq i, fun _ _ h => Matrix.one_apply_ne h.ne'⟩
end Formalism.FourierDecayAlt.P.G4
