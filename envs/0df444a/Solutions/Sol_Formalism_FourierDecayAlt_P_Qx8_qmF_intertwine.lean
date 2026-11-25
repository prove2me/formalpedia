-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.qmF_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:06:18.379724+00:00
-- url     : https://prove2.me/submissions/7264c31e-ff9a-4eab-b9f1-f89fcceed9b0

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key


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
open Topology
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] {n t : ℕ}
    (Eop' : Fin n → Fin n → W' → W') (Eop : Fin n → Fin n → W → W) (A : W' →ₗ[ℂ] W)
    (h : ∀ a b v, A (Eop' a b v) = Eop a b (A v)) (a b : Fin t → Fin n) (u : ℂ) (v : W') :
    A (qmF Eop' a b u v) = qmF Eop a b u (A v) := by
  unfold qmF
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [_root_.map_smul]
  congr 1
  have key : ∀ (L : List (Fin t)) (v : W'),
      A ((L.map fun k : Fin t => fun y : W' =>
        (if a (σ k) = b k then (u - ((k : ℕ) : ℂ)) • y else 0) + Eop' (a (σ k)) (b k) y).foldr (fun T h => T h) v) =
      (L.map fun k : Fin t => fun y : W =>
        (if a (σ k) = b k then (u - ((k : ℕ) : ℂ)) • y else 0) + Eop (a (σ k)) (b k) y).foldr (fun T h => T h)
          (A v) := by
    intro L v
    induction L with
    | nil => rfl
    | cons j L ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [_root_.map_add, h, ih]
      congr 1
      split_ifs
      · rw [_root_.map_smul, ih]
      · rw [_root_.map_zero]
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  exact key _ v
end Formalism.FourierDecayAlt.P.Qx8
