-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.small_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:43.176471+00:00
-- url     : https://prove2.me/submissions/2cfbc1c7-77ed-430a-9f3f-c370075ffceb

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_small
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_isLat_mulR
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x7
theorem _root_.solution (hD : LocalDatum K R ψ) (h0 : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (V : Set K)
    (hV : V ∈ 𝓝 (0 : K)) : ∃ Λ : AddSubgroup K, IsLat Λ ∧ ∀ l ∈ Λ, l ∈ V := by
  obtain ⟨ϖ, hϖ, hϖ'⟩ := hD.unif
  obtain ⟨n, hn⟩ := small hD h0 hϖ hϖ' V hV
  refine ⟨mulR R ((ϖ ^ n : Kˣ) : K), isLat_mulR hD _, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  simpa using hn r hr
end Formalism.FourierDecayAlt.P.A6x7
