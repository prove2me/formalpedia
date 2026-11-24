-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_u_sym
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:31.67108+00:00
-- url     : https://prove2.me/submissions/594413e9-4ecd-44f5-9c9f-b892de8f9204

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_of_vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_sqrt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_sqrt_le_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_model_amplitude_symbol
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_a_zero_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_a_fderiv_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ Cχ S : ℝ} {φ : (Fin d → ℂ) → ℝ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hr : 0 < r) (hρ0 : 0 < ρ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hCχ : 0 ≤ Cχ)
    (hC : ∀ i : ℕ, i ≤ d + 6 → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ)
    {a : (Fin d → ℂ) → V} (ha : ContDiff ℝ (2 * d + 2 : ℕ) a)
    (hbd : ∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) r) (wt (Real.sqrt τ)) 2 (d + 2)
      ((S + 2 ^ (d + 2) * (Cχ * (r + 1) ^ (d + 2)) * (r + 2) * S) * (r + 1) ^ (d + 2)) (E_u d ρ a) := by
  have ha0 := E_a_zero_le hbd
  have hl := E_a_fderiv_le hbd
  have hS : 0 ≤ S := (norm_nonneg _).trans ha0
  have hA1 := model_amplitude_symbol (N := d + 2) hρ0 (fun i hi => hC i (by omega)) hr one_pos le_rfl ha0 hl
  have had : ContDiff ℝ (d + 2 : ℕ) a := ha.of_le (by exact_mod_cast (by omega : d + 2 ≤ 2 * d + 2))
  have hu : E_u d ρ a = a - modelAmplitude d ρ (a 0) (fderiv ℝ a 0) := rfl
  have h := Sym.of_vanish (f := E_u d ρ a) (M := S + 2 ^ (d + 2) * (Cχ * (r + 1) ^ (d + 2)) * (r + 2) * S) 2 hr
    (E_sqrt_pos hτ) (E_sqrt_le_one hτ1) (by omega) (had.sub hA1.1) ?_ ?_
  · exact_mod_cast h
  · intro x hx i hi
    have hin : ((i : ℕ) : WithTop ℕ∞) ≤ (d + 2 : ℕ) := by exact_mod_cast hi
    rw [hu, iteratedFDeriv_sub_apply (had.of_le hin).contDiffAt (hA1.1.of_le hin).contDiffAt]
    refine (norm_sub_le _ _).trans (add_le_add (hbd i (by omega) x) ?_)
    refine (hA1.2 x hx i hi).trans ?_
    have hw1 : (1 : ℝ) ≤ wt 1 x := by unfold wt; linarith [norm_nonneg x]
    have hz : wt 1 x ^ ((0 : ℤ) - (i : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hw1 (by omega)
    have hK : 0 ≤ 2 ^ (d + 2) * (Cχ * (r + 1) ^ (d + 2)) * (r + 2) * S := by positivity
    calc _ ≤ 2 ^ (d + 2) * (Cχ * (r + 1) ^ (d + 2)) * (r + 2) * S * 1 := mul_le_mul_of_nonneg_left hz hK
      _ = _ := mul_one _
  · intro i hi
    have h0 : cutB d ρ (0 : Fin d → ℂ) = 1 := E_cut_one hρ0 (Metric.mem_closedBall_self (by positivity))
    rw [← norm_eq_zero]
    interval_cases i
    · rw [norm_iteratedFDeriv_zero]
      simp [E_u, modelAmplitude, h0]
    · rw [norm_iteratedFDeriv_one]
      have hev : E_u d ρ a =ᶠ[𝓝 0] fun x => a x - (a 0 + fderiv ℝ a 0 x) := by
        filter_upwards [Metric.closedBall_mem_nhds (0 : Fin d → ℂ) (half_pos hρ0)] with x hx
        simp [E_u, modelAmplitude, E_cut_one hρ0 hx]
      rw [hev.fderiv_eq]
      have hda : HasFDerivAt a (fderiv ℝ a 0) 0 :=
        ((had.differentiable (by simp)) 0).hasFDerivAt
      have h3 : HasFDerivAt (fun x => a x - (a 0 + fderiv ℝ a 0 x)) (fderiv ℝ a 0 - fderiv ℝ a 0) 0 :=
        hda.sub ((fderiv ℝ a 0).hasFDerivAt.const_add (a 0))
      rw [h3.fderiv, sub_self, norm_zero]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
