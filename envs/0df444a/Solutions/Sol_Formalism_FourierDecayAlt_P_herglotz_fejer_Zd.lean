-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.herglotz_fejer_Zd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:56.198126+00:00
-- url     : https://prove2.me/submissions/00cc06e5-d35f-4937-9320-1ea2f33d8a5f

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FacSuccOfNotMem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fejer_wt_succ_of_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fejer_wt_succ_of_not_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_dsum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_ee_mul_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_wt_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Real Finset Formalism.FourierDecayAlt.P.Herglotz Formalism.FourierDecayAlt.P.Fejer
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.H.HerglotzFejerZd := by
  intro d A hPD N x
  have h := hPD (box d (N + 1)) (ee x)
  simp_rw [mul_assoc, ee_mul_conj] at h
  have hd := dsum (fun τ => A τ * ee x τ) (box d (N + 1))
  beta_reduce at hd
  rw [hd] at h
  have hN0 : N + 1 ≠ 0 := by omega
  have heq : (∑' τ, ((wt (N + 1) τ : ℝ) : ℂ) * (A τ * ee x τ)) =
      (((((N + 1 : ℕ) : ℝ) ^ d)⁻¹ : ℝ) : ℂ) *
        ∑' τ, (((box d (N + 1) ×ˢ box d (N + 1)).filter (fun p => p.1 - p.2 = τ)).card : ℂ) *
          (A τ * ee x τ) := by
    rw [← tsum_mul_left]
    congr 1
    funext τ
    rw [← wt_eq (N + 1) hN0 τ]
    push_cast
    ring
  have hfin : (∑' τ, ((wt (N + 1) τ : ℝ) : ℂ) * (A τ * ee x τ)) =
      ∑ σ ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N),
        (((∏ j, (1 - |((σ j : ℤ) : ℝ)| / ((N : ℝ) + 1))) : ℝ) : ℂ) * A σ *
          Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ)) := by
    rw [tsum_eq_sum (s := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N))]
    · refine Finset.sum_congr rfl (fun σ hσ => ?_)
      rw [wt_succ_of_mem N σ hσ, mul_assoc]
      rfl
    · intro τ hτ
      rw [wt_succ_of_not_mem N τ hτ]
      simp
  rw [← hfin, heq, Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) h
end Formalism.FourierDecayAlt.P
