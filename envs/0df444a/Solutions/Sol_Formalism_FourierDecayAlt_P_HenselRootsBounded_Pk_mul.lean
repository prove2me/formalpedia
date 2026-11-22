-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.Pk_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:44:20.098122+00:00
-- url     : https://prove2.me/submissions/490fbcdb-cb8e-49aa-b624-d592b9989b57

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_mem_Pk

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
theorem _root_.solution {k l : ℤ} {x y : K} (hx : x ∈ Pk R ϖ k) (hy : y ∈ Pk R ϖ l) :
    x * y ∈ Pk R ϖ (k + l) := by
  rw [mem_Pk] at *
  have : ((ϖ ^ (-(k + l)) : Kˣ) : K) * (x * y) =
      (((ϖ ^ (-k) : Kˣ) : K) * x) * (((ϖ ^ (-l) : Kˣ) : K) * y) := by
    rw [neg_add, zpow_add, Units.val_mul]; ring
  rw [this]; exact R.mul_mem hx hy
end Formalism.FourierDecayAlt.P.HenselRootsBounded
