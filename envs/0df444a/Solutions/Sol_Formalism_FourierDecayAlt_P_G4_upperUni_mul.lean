-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.upperUni_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:42.167623+00:00
-- url     : https://prove2.me/submissions/8dd9ab16-99dd-4633-8ace-6baa08c32d5d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_tri_mul_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_tri_mul

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
theorem _root_.solution {d : ℕ} {p q : Matrix (Fin d) (Fin d) ℂ} (hp : IsUpperUni p) (hq : IsUpperUni q) :
    IsUpperUni (p * q) :=
  ⟨fun i => by rw [tri_mul_diag hp.2 hq.2, hp.1, hq.1, mul_one], tri_mul hp.2 hq.2⟩
end Formalism.FourierDecayAlt.P.G4
