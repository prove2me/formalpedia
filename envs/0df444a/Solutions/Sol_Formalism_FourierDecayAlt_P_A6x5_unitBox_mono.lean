-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x5.unitBox_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:22.107752+00:00
-- url     : https://prove2.me/submissions/944afd83-e45d-4042-8099-9b2de2b5fe07

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x5
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x5
theorem _root_.solution (ϖ : Kˣ) (hϖR : (ϖ : K) ∈ R) {j j' : ℕ} (h : j ≤ j') :
    unitBox R ϖ j ⊆ unitBox R ϖ j' := by
  rintro z ⟨y, hzy, hz, hy⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨y, hzy, ?_, ?_⟩
  · rw [pow_add, mul_comm ((ϖ : K) ^ j), mul_assoc]
    exact R.mul_mem (R.pow_mem hϖR _) hz
  · rw [pow_add, mul_comm ((ϖ : K) ^ j), mul_assoc]
    exact R.mul_mem (R.pow_mem hϖR _) hy
end Formalism.FourierDecayAlt.P.A6x5
