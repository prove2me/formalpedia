-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.powU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:30.634007+00:00
-- url     : https://prove2.me/submissions/49914d52-9910-425c-8681-2343f2887be8

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_mulU

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
theorem _root_.solution (h : Ctx K R ϖ) {n : ℤ} (hn : 0 ≤ n) {x : K} (hx : x - 1 ∈ Pk R ϖ n) (i : ℕ) :
    x ^ i - 1 ∈ Pk R ϖ n := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ]; exact mulU h hn ih hx
end Formalism.FourierDecayAlt.P.HenselRootsBounded
