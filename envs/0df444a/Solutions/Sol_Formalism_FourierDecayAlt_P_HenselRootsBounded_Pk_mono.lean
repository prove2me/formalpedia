-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.Pk_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:44:13.766488+00:00
-- url     : https://prove2.me/submissions/15aed59e-c596-40c1-8a18-6b6b02b52f7d

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
theorem _root_.solution (hϖ : (ϖ : K) ∈ R) {k l : ℤ} (h : l ≤ k) {x : K} (hx : x ∈ Pk R ϖ k) :
    x ∈ Pk R ϖ l := by
  obtain ⟨n, rfl⟩ := Int.le.dest h
  rw [mem_Pk] at *
  have : ((ϖ ^ (-l) : Kˣ) : K) * x = (ϖ : K) ^ n * (((ϖ ^ (-(l + n)) : Kˣ) : K) * x) := by
    rw [← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
    congr 3; ring
  rw [this]; exact R.mul_mem (R.pow_mem hϖ n) hx
end Formalism.FourierDecayAlt.P.HenselRootsBounded
