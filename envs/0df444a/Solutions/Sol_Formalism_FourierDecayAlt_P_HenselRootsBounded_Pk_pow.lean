-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.Pk_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:30.516211+00:00
-- url     : https://prove2.me/submissions/bbfcf4a4-1a5c-42d7-a7b4-0a781c798f28

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
theorem _root_.solution {k : ℤ} {x : K} (hx : x ∈ Pk R ϖ k) (n : ℕ) : x ^ n ∈ Pk R ϖ (n * k) := by
  induction n with
  | zero => simpa using (Pk_zero (R := R) (ϖ := ϖ)).2 R.one_mem
  | succ n ih =>
    have := Pk_mul ih hx
    rw [pow_succ]; convert this using 2; push_cast; ring
end Formalism.FourierDecayAlt.P.HenselRootsBounded
