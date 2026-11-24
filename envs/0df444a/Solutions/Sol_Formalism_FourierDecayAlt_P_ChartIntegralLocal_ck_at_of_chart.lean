-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChartIntegralLocal.ck_at_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:38:42.690107+00:00
-- url     : https://prove2.me/submissions/36493d96-3a6c-4692-baa8-e2a156c47427

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChartIntegralLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_Mv_co
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_co_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_iot_facts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_prj_of_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_rho_cd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_sr_open
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mono
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChartIntegralLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
namespace Formalism.FourierDecayAlt.P.ChartIntegralLocal
theorem _root_.solution {F : Mat k r → E} {mm : ℕ} {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {δ : ℝ} (hδ : 0 < δ)
    (hAL : ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Metric.ball 0 δ)) :
    ∃ (U : Set (Mat k r)) (F' : Mat k r → E), IsOpen U ∧ g0 ∈ U ∧
      ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) F' U ∧ ∀ g ∈ U, g ∈ GV k r → F g = F' g := by
  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  set U := Sr g0 ∩ Formalism.FourierDecayAlt.P.Ux10.rho g0 ⁻¹' Metric.ball (0 : J k r → ℝ) δ with hUdef
  have hUo : IsOpen U :=
    (rho_cd g0).continuousOn.isOpen_inter_preimage (sr_open g0) Metric.isOpen_ball
  have hg0U : g0 ∈ U := by
    have h2 : (1 + 1 : Mat k r) = (2 : ℂ) • (1 : Mat k r) := by rw [two_smul]
    refine ⟨?_, ?_⟩
    · show IsUnit (g0 * g0⁻¹ + 1).det
      rw [hg1, h2, Matrix.det_smul, Matrix.det_one, mul_one]
      exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _
    · show Formalism.FourierDecayAlt.P.Ux10.rho g0 g0 ∈ Metric.ball (0 : J k r → ℝ) δ
      have h3 : Formalism.FourierDecayAlt.P.Ux10.rho g0 g0 = 0 := by
        funext i
        simp only [Formalism.FourierDecayAlt.P.Ux10.rho, hg1, iot, sub_self, Matrix.zero_mul]
        exact co_zero i
      rw [h3]; exact Metric.mem_ball_self hδ
  refine ⟨U, fun x => F (chart g0 (Formalism.FourierDecayAlt.P.Ux10.rho g0 x)), hUo, hg0U, ?_, ?_⟩
  · have h4 : ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (Formalism.FourierDecayAlt.P.Ux10.rho g0) U :=
      ((rho_cd g0).mono Set.inter_subset_left).of_le (by exact_mod_cast le_top)
    exact hAL.comp h4 (by intro x hx; exact hx.2)
  · intro x hx hxG
    have hh : x * g0⁻¹ ∈ GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hxG (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg0)
    obtain ⟨hl, -, hk⟩ := iot_facts hh hx.1
    show F x = F (kap (prj (Mv (co (iot (x * g0⁻¹))))) * g0)
    rw [Mv_co, prj_of_lie hl, hk, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.ChartIntegralLocal
