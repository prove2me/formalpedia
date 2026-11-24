-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_u_bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:05.436357+00:00
-- url     : https://prove2.me/submissions/9ffef599-f6e0-4a8d-b8ab-c189c99fbc29

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_holo_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_norm_iteratedFDerivWithin_real_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_norm_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_u_contDiffOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {d q : ℕ} {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} {P : ℝ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) {x : Fin d → ℂ} (hx : x ∈ Ω)
    (hb : ∀ j : ℕ, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℂ (j + 1) g x‖ ≤ ‖fderiv ℂ g x‖ * P ^ j) (k : Fin d) :
    Bd (fun x => fderiv ℂ g x (Pi.single k 1)) Ω x q ‖fderiv ℂ g x‖ P := by
  intro j hj
  rw [norm_iteratedFDerivWithin_real_eq hΩ (bkb_u_contDiffOn hΩ hg k q) hx hj,
    iteratedFDerivWithin_of_isOpen j hΩ hx]
  have h := holo_contDiffOn hΩ hg (q + 1)
  have h' : ContDiffOn ℂ ((q : WithTop ℕ∞) + 1) g Ω := by exact_mod_cast h
  have h2 := ((contDiffOn_succ_iff_fderiv_of_isOpen hΩ).mp h').2.2
  have h3 := (ContinuousLinearMap.apply ℂ ℂ (Pi.single k (1 : ℂ) : Fin d → ℂ)).norm_iteratedFDeriv_comp_left
    (h2.contDiffAt (hΩ.mem_nhds hx)) (n := j) (by exact_mod_cast hj)
  have h4 : ‖ContinuousLinearMap.apply ℂ ℂ (Pi.single k (1 : ℂ) : Fin d → ℂ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
    have := T.le_opNorm (Pi.single k (1 : ℂ) : Fin d → ℂ)
    rw [bkb_norm_single, mul_one] at this
    simpa using this
  have h5 : ‖iteratedFDeriv ℂ (j + 1) g x‖ ≤ ‖fderiv ℂ g x‖ * P ^ j := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [norm_iteratedFDeriv_one]
    · exact hb j hj0 hj
  rw [norm_iteratedFDeriv_fderiv] at h3
  calc _ ≤ _ := h3
    _ ≤ 1 * ‖iteratedFDeriv ℂ (j + 1) g x‖ := mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h5
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
