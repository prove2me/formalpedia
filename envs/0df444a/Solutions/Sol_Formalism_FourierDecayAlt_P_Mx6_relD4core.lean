-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.relD4core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:08:55.937361+00:00
-- url     : https://prove2.me/submissions/a50ac0ef-92fc-47fe-8cd2-15c8358672b2

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lA_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_commutator_identity_four
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_scalar_partial_fraction_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_Lam4
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_sc_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lowering_constant_eq_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Lam_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Lams_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_N_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Ns_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Ns_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_N_cz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_G_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_G_cz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_cz_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_G_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Ns_Lam
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_N_Lams
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_mt_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Lam_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Lam_cz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Lams_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Lams_cz

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
theorem _root_.solution (hN : SSNorm) (hM : SSMixed) (hS : NabSS) (hK : Curvature) (hP : P.OK)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (mt P u * lA P v - lA P v * mt P u) = kap P (hh P v - hh P u) * (ggiA P * ggiA P) := by
  have hcurv : nabsA P * nabA P = nabA P * nabsA P +
      (kap P fun π => ((2 * aC P π * P.TT : ℝ) : ℂ)) * (ggiA P * ggiA P) := by
    rw [← mul_assoc, ← hK P]; abel
  have h := commutator_identity_four (nabA P) (nabsA P) (cc P) (cz P) (ggiA P) (kap P fun π => ((2 * aC P π * P.TT : ℝ) : ℂ))
    (Lams P u) (abelian₂ P v) (u + 1 / 2) (v + 1 / 2) (P.TT : ℂ) hcurv (Ns_cc P) (N_cz P) (N_G P) (Ns_G P)
    (Ns_Lam P hS v) (N_Lams P hS u) (G_cc P) (G_cz P) (cz_cc P) (Lam_cc P v) (Lam_cz P v) (Lam_sc P _ _)
    (Lams_cc P u) (Lams_cz P u) (Lams_sc P _ _)
  rw [mt_eq, lA_eq, lowering_constant_eq_shift, h, L4.Lam4 P hP u v hN hM]
  have e1 : ∀ f : Ty P → ℂ, ggiA P * (ggiA P * kap P f) = kap P f * (ggiA P * ggiA P) := fun f => by
    rw [← mul_assoc, G_sc, sc_mul, kap_sc]
  have e2 : ∀ z : ℂ, z • (ggiA P * ggiA P) = kap P (fun _ => z) * (ggiA P * ggiA P) := fun z => by
    have : kap P (fun _ => z) = algebraMap ℂ (A P) z := (kap P).commutes z
    rw [this, Algebra.smul_def]
  rw [e1, e2, ← add_mul, ← add_mul, ← map_add, ← map_add, ← smul_mul_assoc, ← map_smul]
  congr 2
  funext π
  have hs := WB.scalar_partial_fraction_identity P hP π u v hu hv
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hh]
  rw [← hs]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.Mx6
