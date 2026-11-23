-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.model_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:07.546946+00:00
-- url     : https://prove2.me/submissions/bedab7d1-7b41-433e-ac1b-854b2ce910eb

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_rootA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_rootB
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_rc_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_weight_model_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_q_eval
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_ord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_realPoints
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rho_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_tyInterlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_tyInterlaces


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.WB
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx6.WB
theorem _root_.solution (P : Par) (hP : P.OK) (π : Ty P) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    (wNum P π /ₘ coordinatePolynomial P π).eval (-(rc P π l)) = (((Nrm P l π : ℝ) : ℂ) - ((NrmDown P l π : ℝ) : ℂ)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rc P π j - rc P π l) := by
  have hl' := Finset.mem_Icc.1 hl
  by_cases hdeg : ∃ j0 ∈ (Icc 1 (P.k - 1)).erase l, rho P π j0 + 1 = rho P π l
  · obtain ⟨j0, hj0, hρ⟩ := hdeg
    have hj0' := Finset.mem_erase.1 hj0
    have hNd : NrmDown P l π = 0 := by
      unfold NrmDown
      have hz : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1) = 0 :=
        Finset.prod_eq_zero hj0 (by linarith)
      rw [hz, zero_mul, div_zero]
    have hN0 : Nrm P j0 π = 0 := by
      unfold Nrm
      have hz : ∏ j ∈ (Icc 1 (P.k - 1)).erase j0, (rho P π j - rho P π j0 - 1) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.2 ⟨fun e => hj0'.1 e.symm, hl⟩) (by linarith)
      rw [hz, mul_zero, div_zero]
    have hI := Mx3.tyInterlaces P hP π
    have hlt : l < j0 := by
      by_contra hcon
      have : j0 < l := lt_of_le_of_ne (not_lt.1 hcon) hj0'.1
      have := Mx3.rho_inj P hP π j0 l hj0'.2 hl this
      linarith
    have o := (Mx3.ord P.k P.u P.u' (rho P π) hI l hl).2.2.2 j0 hj0'.2 hlt
    have b := hI l hl
    have hu : P.u (l + 1) = rho P π l - 1 / 2 := by linarith [o.1, b.2.2.1]
    have hu' : P.u' (l + 1) = rho P π l - 1 / 2 := by linarith [o.2, b.2.2.2]
    have hq : (X + C (rc P π l)) ^ 2 ∣ C (-((P.T : ℂ) * P.T')) * q1P P := by
      apply Dvd.dvd.mul_left
      have hm : l + 1 ∈ Icc 1 P.k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have hd := Finset.dvd_prod_of_mem
        (fun i => ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))) : ℂ[X])) hm
      have e1 : (1 / 2 + (P.u (l + 1) : ℂ)) = rc P π l := by rw [hu]; unfold rc; push_cast; ring
      have e2 : (1 / 2 + (P.u' (l + 1) : ℂ)) = rc P π l := by rw [hu']; unfold rc; push_cast; ring
      simp only [e1, e2] at hd
      rw [pow_two]
      exact hd
    have := rootB (weight_model_identity P hP π) (rc_inj P hP π) hl hj0'.2 hj0'.1
      (by unfold rc; exact_mod_cast hρ) hq (by simp only [hN0]; simp)
    rw [this, hNd]; simp
  · push Not at hdeg
    have hA1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j hj h0
      exact hdeg j hj (by linarith)
    have hA0 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j hj h0
      have hj' := Finset.mem_erase.1 hj
      apply hj'.1
      apply rc_inj P hP π j hj'.2 l hl
      unfold rc
      have : rho P π j = rho P π l := by linarith
      rw [this]
    have hk : NrmDown P l π * ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1)) *
        ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) = -I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l) := by
      unfold NrmDown
      exact div_mul_cancel₀ _ (mul_ne_zero hA1 hA0)
    have hk' := congrArg (fun x : ℝ => (x : ℂ)) hk
    simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_neg,
      Complex.ofReal_one] at hk'
    have hA1c : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rc P π j - rc P π l + 1) ≠ 0 := by
      have := hA1
      unfold rc
      intro h0
      apply this
      exact_mod_cast h0
    refine rootA (fun l => ((NrmDown P l π : ℝ) : ℂ)) (weight_model_identity P hP π) hl hA1c ?_
    rw [q_eval]
    have hr := (Mx3.realPoints P π (-rho P π l)).2
    have e : (((-rho P π l : ℝ)) : ℂ) = -(rc P π l) := by unfold rc; push_cast; ring
    rw [e] at hr
    rw [hr]
    exact hk'
end Formalism.FourierDecayAlt.P.Mx6.WB
