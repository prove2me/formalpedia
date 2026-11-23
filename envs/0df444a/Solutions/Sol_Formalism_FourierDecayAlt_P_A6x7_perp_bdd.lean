-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.perp_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:43.126336+00:00
-- url     : https://prove2.me/submissions/285ff89e-38de-4947-9f5a-ec25f8569c5e

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_small
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_compact_big

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x7
theorem _root_.solution (hD : LocalDatum K R ψ) (h0 : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (L : AddSubgroup K)
    (hL : IsLat L) : ∃ C : Set K, IsCompact C ∧ ∀ y ∈ perp ψ L, y ∈ C := by
  obtain ⟨ϖ, hϖ, hϖ'⟩ := hD.unif
  obtain ⟨n, hn⟩ := small hD h0 hϖ hϖ' (L : Set K) (hL.1.mem_nhds L.zero_mem)
  refine ⟨_, compact_big hD ϖ n, fun y hy => ?_⟩
  apply (hD.selfDual _).1
  intro r hr
  have := hy _ (hn r hr)
  rw [← this]; congr 1; ring
end Formalism.FourierDecayAlt.P.A6x7
