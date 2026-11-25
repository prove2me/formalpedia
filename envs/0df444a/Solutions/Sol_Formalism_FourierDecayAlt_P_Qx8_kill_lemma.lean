-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.kill_lemma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:54:19.276654+00:00
-- url     : https://prove2.me/submissions/454a5018-4eff-48d4-9f51-77b790ad3a45

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulIntegralStatement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_Rep_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_piL_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_piL_eig
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.M
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution {W ι : Type*} [AddCommGroup W] [Module ℂ W] [Fintype ι] (S : ι → Submodule ℂ W)
    (hS : ⨆ τ, S τ = ⊤) (L : ι → W → W) (hL : ∀ τ, IsLin (L τ)) (lam : ι → ι → ℂ)
    (hlam : ∀ τ τ', ∀ w ∈ S τ', L τ w = lam τ τ' • w) (μ : ι → ℂ) {u : W} (hu : ∀ τ, L τ u = μ τ • u)
    (hne : ∀ τ, μ τ ≠ lam τ τ) : u = 0 := by
  set c : ι → ℂ := fun τ => lam τ τ with hc
  set l := (Finset.univ : Finset ι).toList with hl
  have hlin := piL_lin L hL c l
  have hzero : ∀ w, piL L c l w = 0 := by
    intro w
    have hw : w ∈ ⨆ τ, S τ := by rw [hS]; trivial
    induction hw using Submodule.iSup_induction' with
    | mem τ' w hw =>
      rw [piL_eig L hL c (fun τ => lam τ τ') (fun τ => hlam τ τ' w hw) l]
      have : (l.map fun τ => lam τ τ' - c τ).prod = 0 := by
        apply List.prod_eq_zero
        rw [List.mem_map]
        exact ⟨τ', by simp [hl], by simp [hc]⟩
      rw [this, zero_smul]
    | zero => exact hlin.map_zero
    | add a b _ _ ha hb => rw [hlin.map_add, ha, hb, add_zero]
  have h1 := piL_eig L hL c μ hu l
  rw [hzero] at h1
  have hp : (l.map fun τ => μ τ - c τ).prod ≠ 0 := by
    apply List.prod_ne_zero
    rw [List.mem_map]
    rintro ⟨τ, -, h0⟩
    exact hne τ (sub_eq_zero.1 h0)
  exact (smul_eq_zero.1 h1.symm).resolve_left hp
end Formalism.FourierDecayAlt.P.Qx8
