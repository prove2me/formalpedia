-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.Pk_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:47:44.966683+00:00
-- url     : https://prove2.me/submissions/2c5eb96f-1db3-40b8-9251-eb8dd8bfa31d

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K] {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution {k : ℤ} {x r : K} (hx : x ∈ Pk R ϖ k) (hr : r ∈ R) : x * r ∈ Pk R ϖ k := by
  have := Pk_mul hx (Pk_zero.2 hr); simpa using this
end Formalism.FourierDecayAlt.P.HenselRootsBounded
