-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.limit_ck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:01:35.652938+00:00
-- url     : https://prove2.me/submissions/1a528063-11c2-4c62-9cb8-96afeb08080e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_AL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_prj_of_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_iot_facts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_Mv_co
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_co_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_Lt_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_dom_open
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_zero_mem_dom
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_chart_cd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_chart_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_aC_cd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_hasFDeriv_chart
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_tuo_of_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_continuous_gN
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cont_chart
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_sr_open
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_rho_cd
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_allLie_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_smooth_on_of_word_derivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {a : ℝ} {mm : ℕ} (Fs : ℕ → Mat k r → E)
    (hC : ∀ n, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (Fs n))
    (K : List (Mat k r) → List (Mat k r) → Mat k r → E) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hε0 : ∀ n, 0 ≤ ε n)
    (hb : ∀ n (u w : List (Mat k r)), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ w, unitLie k r X) →
      u.length + w.length ≤ mm → ∀ g ∈ GV k r, ‖dLR u w (Fs n) g - K u w g‖ ≤ gN g ^ (-a) * ε n) :
    CkOn ((mm : ℕ) : ℕ∞) (GV k r) (K [] []) := by
  intro g0 hg0

  obtain ⟨δ0, hδ0, hball⟩ := Metric.mem_nhds_iff.1 (dom_open.mem_nhds (zero_mem_dom (k := k) (r := r)))
  set δ := δ0 / 2 with hδ
  have hcl : Metric.closedBall (0 : J k r → ℝ) δ ⊆ Dom k r :=
    (Metric.closedBall_subset_ball (by rw [hδ]; linarith)).trans hball
  have hΩ : Metric.ball (0 : J k r → ℝ) δ ⊆ Dom k r := Metric.ball_subset_closedBall.trans hcl
  have hcomp : IsCompact (Metric.closedBall (0 : J k r → ℝ) δ) := isCompact_closedBall _ _

  have hwc : ContinuousOn (fun Y => gN (chart g0 Y) ^ (-a)) (Metric.closedBall (0 : J k r → ℝ) δ) :=
    (continuous_gN.comp_continuousOn ((chart_cd g0).continuousOn.mono hcl)).rpow_const
      fun Y hY => Or.inl (gN_pos (chart_mem hg0 (hcl hY))).ne'
  obtain ⟨Bw, hBw⟩ := hcomp.exists_bound_of_continuousOn hwc

  have hac : ContinuousOn (fun Y => ∑ i, ‖aC g0 i Y‖) (Metric.closedBall (0 : J k r → ℝ) δ) :=
    continuousOn_finsetSum _ fun i _ => ((aC_cd hg0 i).continuousOn.mono hcl).norm
  obtain ⟨Ba, hBa⟩ := hcomp.exists_bound_of_continuousOn hac
  have hBa' : ∀ i, ∀ Y ∈ Metric.ball (0 : J k r → ℝ) δ, ‖aC g0 i Y‖ ≤ Ba := by
    intro i Y hY
    have h1 := hBa Y (Metric.ball_subset_closedBall hY)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
    exact (Finset.single_le_sum (f := fun i => ‖aC g0 i Y‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)).trans h1
  have hunit : ∀ w : List (J k r), ∀ X ∈ w.map Lt, unitLie k r X := by
    intro w X hX
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hX
    exact Lt_unit i
  have hckw : ∀ n (w : List (J k r)) (m : ℕ), m + w.length ≤ mm →
      CkOn ((m : ℕ) : ℕ∞) (GV k r) (dLR (w.map Lt) [] (Fs n)) := by
    intro n w m hm
    rw [dLR_eq]
    exact smooth_on_of_word_derivatives _ (allLie_lr (hunit w) (by simp)) m
      (ckOn_mono (by rw [length_lr]; simp; omega) (hC n))
  have hAL := AL (𝔤 := J k r → ℝ) (E := E) Metric.isOpen_ball (aC g0)
    (fun i => (aC_cd hg0 i).mono hΩ) Ba hBa' mm
    (fun w n Y => dLR (w.map Lt) [] (Fs n) (chart g0 Y)) (fun w Y => K (w.map Lt) [] (chart g0 Y))
    (fun w hw n => (cont_chart hg0 (hckw n w 0 (by omega))).mono hΩ)
    (fun w hw n Y hY => hasFDeriv_chart hg0 (hckw n w 1 (by omega)) (hΩ hY))
    (fun w hw => tuo_of_bound hε fun n Y hY => by
      refine (hb n (w.map Lt) [] (hunit w) (by simp) (by simpa using hw) _ (chart_mem hg0 (hΩ hY))).trans ?_
      have h1 := hBw Y (Metric.ball_subset_closedBall hY)
      rw [Real.norm_eq_abs] at h1
      exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans h1) (hε0 n))

  have hgu : IsUnit g0.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg0
  have hg1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  set U := Sr g0 ∩ rho g0 ⁻¹' Metric.ball (0 : J k r → ℝ) δ with hUdef
  have hUo : IsOpen U := (rho_cd g0).continuousOn.isOpen_inter_preimage (sr_open g0) Metric.isOpen_ball
  have hg0U : g0 ∈ U := by
    have h2 : (1 + 1 : Mat k r) = (2 : ℂ) • (1 : Mat k r) := by rw [two_smul]
    refine ⟨?_, ?_⟩
    · show IsUnit (g0 * g0⁻¹ + 1).det
      rw [hg1, h2, Matrix.det_smul, Matrix.det_one, mul_one]
      exact (isUnit_iff_ne_zero.2 two_ne_zero).pow _
    · show rho g0 g0 ∈ Metric.ball (0 : J k r → ℝ) δ
      have h3 : rho g0 g0 = 0 := by
        funext i
        simp only [rho, hg1, iot, sub_self, Matrix.zero_mul]
        exact co_zero i
      rw [h3]; exact Metric.mem_ball_self (by rw [hδ]; linarith)
  refine ⟨U, fun x => K [] [] (chart g0 (rho g0 x)), hUo, hg0U, ?_, ?_⟩
  · have h4 : ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (rho g0) U :=
      ((rho_cd g0).mono Set.inter_subset_left).of_le (by exact_mod_cast le_top)
    exact hAL.comp h4 (by intro x hx; exact hx.2)
  · intro x hx hxG
    have hh : x * g0⁻¹ ∈ GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hxG (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg0)
    obtain ⟨hl, -, hk⟩ := iot_facts hh hx.1
    show K [] [] x = K [] [] (kap (prj (Mv (co (iot (x * g0⁻¹))))) * g0)
    rw [Mv_co, prj_of_lie hl, hk, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hgu, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.Ux1
