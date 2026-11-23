-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_gau_one_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:57.295351+00:00
-- url     : https://prove2.me/submissions/7385b4ad-dd5d-44ac-b19e-5350ddac31ff

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_wt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_nsq_sym
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_norm_sq_le_nsq
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_exp_decay
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_norm_iter_exp
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_gau_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
noncomputable section
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d n : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Fin d → ℂ,
    (1 + ‖x‖) ^ n * ‖iteratedFDeriv ℝ n (D_gau d 1) x‖ ≤ M := by
  obtain ⟨K, hK, hS⟩ := D_nsq_sym d n
  refine ⟨n.factorial * (K + 1) ^ n * (2 ^ n * n.factorial * Real.exp 1), by positivity, fun x => ?_⟩
  have hS' := hS.neg
  have hb : ‖iteratedFDeriv ℝ n (D_gau d 1) x‖ ≤
      n.factorial * Real.exp (- D_nsq d x) * ((K + 1) * (1 + ‖x‖)) ^ n := by
    rw [D_gau_one_eq]
    refine norm_iteratedFDeriv_comp_le (N := (n : ℕ)) Real.contDiff_exp hS'.1 le_rfl x
      (fun i _ => (D_norm_iter_exp i _).le) (fun i hi1 hin => ?_)
    have h1 := hS'.2 x (Set.mem_univ x) i hin
    have hw1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have h2 : wt (1 : ℝ) x ^ ((2 : ℤ) - (i : ℤ)) ≤ (1 + ‖x‖) ^ i := by
      have : wt (1 : ℝ) x = 1 + ‖x‖ := by unfold wt; ring
      rw [this, ← zpow_natCast]
      exact zpow_le_zpow_right₀ hw1 (by omega)
    have h3 : K ≤ (K + 1) ^ i := by
      calc K ≤ K + 1 := by linarith
        _ ≤ (K + 1) ^ i := le_self_pow₀ (by linarith) (by omega)
    calc _ ≤ K * wt (1 : ℝ) x ^ ((2 : ℤ) - (i : ℤ)) := h1
      _ ≤ (K + 1) ^ i * (1 + ‖x‖) ^ i := by
        apply mul_le_mul h3 h2 (zpow_nonneg (D_wt_pos one_pos x).le _) (by positivity)
      _ = ((K + 1) * (1 + ‖x‖)) ^ i := by rw [mul_pow]
  have he : Real.exp (- D_nsq d x) ≤ Real.exp (- ‖x‖ ^ 2) :=
    Real.exp_le_exp.2 (neg_le_neg (D_norm_sq_le_nsq d x))
  calc (1 + ‖x‖) ^ n * ‖iteratedFDeriv ℝ n (D_gau d 1) x‖
      ≤ (1 + ‖x‖) ^ n * (n.factorial * Real.exp (- ‖x‖ ^ 2) * ((K + 1) * (1 + ‖x‖)) ^ n) := by
        gcongr
        exact hb.trans (by gcongr)
    _ = n.factorial * (K + 1) ^ n * ((1 + ‖x‖) ^ (2 * n) * Real.exp (- ‖x‖ ^ 2)) := by
        rw [mul_pow, two_mul, pow_add]; ring
    _ ≤ n.factorial * (K + 1) ^ n * (2 ^ n * n.factorial * Real.exp 1) := by
        exact mul_le_mul_of_nonneg_left (D_exp_decay n ‖x‖ (norm_nonneg x)) (by positivity)
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
