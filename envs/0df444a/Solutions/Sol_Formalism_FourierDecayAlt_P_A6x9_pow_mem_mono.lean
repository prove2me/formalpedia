-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x9.pow_mem_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:06:58.909388+00:00
-- url     : https://prove2.me/submissions/b12b6b68-7740-499c-932c-88db5e1d8cc7

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x9
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable (π : Kˣ)
namespace Formalism.FourierDecayAlt.P.A6x9
theorem _root_.solution (hπ : (π : K) ∈ R) {k k' : ℕ} (h : k ≤ k') {z : K} (hz : (π : K) ^ k * z ∈ R) :
    (π : K) ^ k' * z ∈ R := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  have : (π : K) ^ (k + j) * z = (π : K) ^ j * ((π : K) ^ k * z) := by ring
  rw [this]
  exact R.mul_mem (R.pow_mem hπ j) hz
end Formalism.FourierDecayAlt.P.A6x9
