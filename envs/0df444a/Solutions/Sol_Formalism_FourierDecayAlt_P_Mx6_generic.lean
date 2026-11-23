-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.generic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:12.297535+00:00
-- url     : https://prove2.me/submissions/9536887c-91ce-448b-b6d5-7018c20ccd48

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_GA_gauss_rtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lowering_relation_diagonal_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lowering_relation_diagonal_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_commutator_l_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_mixed_relation_diagonal_four
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_commutator_t22_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_commutator_d_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_raising_relation_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_nf21
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_nf12
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_nf11
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_comm_tt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_comm_dd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_comm_dt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution (hN : SSNorm) (hC : SSComm) (hM : SSMixed) (hS : NabSS) (hK : Curvature) (hP : P.OK)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) (h0 : u - v ≠ 0) (h1 : u - v ≠ 1) (h2 : u - v ≠ -1)
    (i j k l : Fin 2) :
    (u - v) • (QQr P u i j * QQr P v k l - QQr P v k l * QQr P u i j) =
      QQr P u k j * QQr P v i l - QQr P v k j * QQr P u i l := by
  have eU : ∀ {y : ℂ}, Good P y → QQr P y =
      !![dA P y + mt P y * t22 P y * lA P y, mt P y * t22 P y; t22 P y * lA P y, t22 P y] := fun {y} hy => by
    rw [QQr, nf11 P hN hP hy, nf12 P hy, nf21 P hy]
  have e : v - u = -(u - v) := by ring
  rw [eU hu, eU hv]
  refine GA.gauss_rtt (u - v) h0 h1 h2 (t22 P u) (t22 P v) (dA P u) (dA P v) (lA P u) (lA P v) (mt P u) (mt P v)
    (comm_tt P u v) (comm_dd P u v) (comm_dt P u v) (comm_dt P v u)
    (lowering_relation_diagonal_left P u v hu hv) ?_ (lowering_relation_diagonal_right P u v hu hv) ?_ (commutator_t22_m P u v hu hv) ?_ (commutator_d_m P u v hu hv) ?_
    (commutator_l_sq P hC hS hP u v hu hv) (raising_relation_self P hC hS hP u v hu hv) (mixed_relation_diagonal_four P hN hM hS hK hP u v hu hv) ?_ i j k l
  · have h := lowering_relation_diagonal_left P v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h
  · have h := lowering_relation_diagonal_right P v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h
  · have h := commutator_t22_m P v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h
  · have h := commutator_d_m P v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h
  · have h := mixed_relation_diagonal_four P hN hM hS hK hP v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h
end Formalism.FourierDecayAlt.P.Mx6
