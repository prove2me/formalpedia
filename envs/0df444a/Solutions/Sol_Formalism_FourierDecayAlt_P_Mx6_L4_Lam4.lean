-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L4.Lam4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:29.741439+00:00
-- url     : https://prove2.me/submissions/b5c8f683-e31b-4ff4-9a0d-bdebbdaa7c03

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_S_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_Ss_shift
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Mx6_L4_kap_sum__1aec61f2ed62
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_rr_up_same
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_rr_up_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_rho_unchanged_off_index

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.L4
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6.L4
theorem _root_.solution (hP : P.OK) (u v : ℂ) (hN : SSNorm) (hM : SSMixed) :
    Lams P u * abelian₂ P v - abelian₂ P v * Lams P u = kap P fun π => ∑ j ∈ Icc 1 (P.k - 1),
      (((Nrm P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ) + 1) * (v + (rho P π j : ℂ) + 1)) -
        ((NrmDown P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ)) * (v + (rho P π j : ℂ)))) := by
  rw [kap_sum' P _ (fun j π => ((Nrm P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ) + 1) * (v + (rho P π j : ℂ) + 1)) -
        ((NrmDown P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ)) * (v + (rho P π j : ℂ))))]
  have e1 : Lams P u * abelian₂ P v =
      ∑ i ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1), lams P i u * lam P j v := Finset.sum_mul_sum _ _ _ _
  have e2 : abelian₂ P v * Lams P u =
      ∑ i ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1), lam P j v * lams P i u := by
    unfold Lams abelian₂
    rw [Finset.sum_mul_sum, Finset.sum_comm]
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_sub_distrib]
  have hlam : ∀ j ∈ Icc 1 (P.k - 1), lam P j v = SS P j * kap P (rr1 P j v) := fun j hj =>
    S_shift P j _ _ fun π π' h => rr_up_same P hj h v
  rw [Finset.sum_eq_single_of_mem i hi]
  ·
    have h1 : lams P i u * lam P i v = kap P ((fun π => ((Nrm P i π : ℝ) : ℂ)) * (rr1 P i u * rr1 P i v)) := by
      unfold lams lam
      rw [mul_assoc, ← mul_assoc (kap P _) (kap P _), kap_mul,
        S_shift P i (rr1 P i u * rr1 P i v) _ (fun π π' h => by
          show rr P i u π' * rr P i v π' = rr1 P i u π * rr1 P i v π
          rw [rr_up_same P hi h, rr_up_same P hi h]),
        ← mul_assoc, (hN P hP i hi).1, kap_mul]
    have h2 : lam P i v * lams P i u = kap P (rr P i v * (fun π => ((NrmDown P i π : ℝ) : ℂ)) * rr P i u) := by
      unfold lams lam
      rw [mul_assoc, ← mul_assoc (SS P i), (hN P hP i hi).2, kap_mul, kap_mul, mul_assoc]
    rw [h1, h2, ← map_sub]
    congr 1
    funext π
    simp only [Pi.sub_apply, Pi.mul_apply, rr, rr1]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv]
    ring
  · intro j hj hne
    rw [sub_eq_zero, hlam j hj]
    unfold lams
    have h3 : kap P (rr P i u) * SS P j = SS P j * kap P (rr P i u) :=
      S_shift P j _ _ fun π π' h => rr_up_ne P hi (Ne.symm hne) h u
    have h4 : kap P (rr1 P j v) * star (SS P i) = star (SS P i) * kap P (rr1 P j v) :=
      (Ss_shift P i _ _ fun π π' h => rho_unchanged_off_index P hj hne h v).symm
    calc star (SS P i) * kap P (rr P i u) * (SS P j * kap P (rr1 P j v))
        = star (SS P i) * (kap P (rr P i u) * SS P j) * kap P (rr1 P j v) := by simp only [mul_assoc]
      _ = star (SS P i) * SS P j * (kap P (rr P i u) * kap P (rr1 P j v)) := by rw [h3]; simp only [mul_assoc]
      _ = SS P j * star (SS P i) * (kap P (rr1 P j v) * kap P (rr P i u)) := by
          rw [hM P hP i hi j hj hne, kap_comm]
      _ = SS P j * (star (SS P i) * kap P (rr1 P j v)) * kap P (rr P i u) := by simp only [mul_assoc]
      _ = SS P j * kap P (rr1 P j v) * (star (SS P i) * kap P (rr P i u)) := by rw [← h4]; simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.Mx6.L4
