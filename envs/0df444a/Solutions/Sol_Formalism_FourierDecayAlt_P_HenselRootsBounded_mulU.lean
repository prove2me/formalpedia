-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.mulU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:57:15.729931+00:00
-- url     : https://prove2.me/submissions/0886f65e-e3e9-40f1-82b2-fc4daefe0ad7

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_R

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution (h : Ctx K R ϖ) {n : ℤ} (hn : 0 ≤ n) {x y : K} (hx : x - 1 ∈ Pk R ϖ n)
    (hy : y - 1 ∈ Pk R ϖ n) : x * y - 1 ∈ Pk R ϖ n := by
  have hyR : y ∈ R := by
    have := R.add_mem (Pk_R h.mem hn hy) R.one_mem
    simpa using this
  have := (Pk R ϖ n).add_mem (Pk_smul hx hyR) hy
  convert this using 1; ring
end Formalism.FourierDecayAlt.P.HenselRootsBounded
