-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x9.J_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:23.417846+00:00
-- url     : https://prove2.me/submissions/99699f87-4f7d-4a51-889b-cfc4edcf13ca

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_mem_mulR

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
theorem _root_.solution (hπ : (π : K) ∈ R) {n m : ℕ} (h : n ≤ m) :
    mulR R ((π : K) ^ m) ≤ mulR R ((π : K) ^ n) := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := mem_mulR.1 hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact mem_mulR.2 ⟨(π : K) ^ k * r, R.mul_mem (R.pow_mem hπ k) hr, by ring⟩
end Formalism.FourierDecayAlt.P.A6x9
