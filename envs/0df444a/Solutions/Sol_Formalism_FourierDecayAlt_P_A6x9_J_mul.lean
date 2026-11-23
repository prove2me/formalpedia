-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x9.J_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:33.513118+00:00
-- url     : https://prove2.me/submissions/af56790c-2b11-466f-b75c-f4f7d88604f3

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
theorem _root_.solution {n m : ℕ} {x y : K} (hx : x ∈ mulR R ((π : K) ^ n)) (hy : y ∈ mulR R ((π : K) ^ m)) :
    x * y ∈ mulR R ((π : K) ^ (n + m)) := by
  obtain ⟨q, hq, rfl⟩ := mem_mulR.1 hx
  obtain ⟨r, hr, rfl⟩ := mem_mulR.1 hy
  exact mem_mulR.2 ⟨q * r, R.mul_mem hq hr, by ring⟩
end Formalism.FourierDecayAlt.P.A6x9
