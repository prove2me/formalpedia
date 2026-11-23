-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.holo_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:47.892298+00:00
-- url     : https://prove2.me/submissions/21ce0aa3-ad60-485b-ab8f-0cd9dab8b950

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_C_norm_fderiv_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_C_differentiableOn_fderiv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_holo_contDiffOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Metric
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (i : ℕ) {f : E → F} {x : E} {δ M : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (Metric.ball x ((i + 1 : ℕ) * δ)))
    (hM : ∀ y ∈ Metric.ball x ((i + 1 : ℕ) * δ), ‖f y‖ ≤ M) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ M / δ ^ i := by
  induction i generalizing f M with
  | zero =>
    rw [norm_iteratedFDeriv_zero, pow_zero, div_one]
    exact hM x (mem_ball_self (by positivity))
  | succ i ih =>
    have hpos : 0 < ((i + 1 + 1 : ℕ) : ℝ) * δ := by positivity
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_ball_self hpos))
    have hdf : ∀ y ∈ ball x (((i + 1 + 1 : ℕ) : ℝ) * δ), DifferentiableAt ℂ f y :=
      fun y hy => (hf y hy).differentiableAt (isOpen_ball.mem_nhds hy)
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
    rw [iteratedFDeriv_succ_apply_right]
    set v := m (Fin.last i) with hv
    have hcd : ContDiffAt ℝ ((i + 1 : ℕ) : WithTop ℕ∞) f x :=
      ((holo_contDiffOn isOpen_ball hf (i + 1)).contDiffAt (ball_mem_nhds x hpos)).restrict_scalars ℝ
    have hcd' : ContDiffAt ℝ (i : WithTop ℕ∞) (fderiv ℝ f) x :=
      hcd.fderiv_right (by exact_mod_cast le_rfl)
    have h1 : iteratedFDeriv ℝ i (fderiv ℝ f) x (Fin.init m) v =
        iteratedFDeriv ℝ i (fun y => fderiv ℝ f y v) x (Fin.init m) := by
      have h := (ContinuousLinearMap.apply ℝ F v).iteratedFDeriv_comp_left hcd' le_rfl
      have h' : iteratedFDeriv ℝ i (fun y => fderiv ℝ f y v) x =
          (ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap
            (iteratedFDeriv ℝ i (fderiv ℝ f) x) := h
      rw [h']
      rfl
    have h2 : (fun y => fderiv ℝ f y v) =ᶠ[𝓝 x] fun y => fderiv ℂ f y v := by
      filter_upwards [ball_mem_nhds x hpos] with y hy
      rw [(hdf y hy).fderiv_restrictScalars ℝ]
      rfl
    have hsubb : ball x (((i + 1 : ℕ) : ℝ) * δ) ⊆ ball x (((i + 1 + 1 : ℕ) : ℝ) * δ) := by
      refine ball_subset_ball ?_
      push_cast
      nlinarith
    have h3 := ih (f := fun y => fderiv ℂ f y v) (M := M / δ * ‖v‖)
      ((C_differentiableOn_fderiv_apply isOpen_ball hf v).mono hsubb) (by
        intro y hy
        have hyb : ball y δ ⊆ ball x (((i + 1 + 1 : ℕ) : ℝ) * δ) := by
          refine ball_subset_ball' ?_
          rw [mem_ball] at hy
          push_cast at hy ⊢
          linarith
        have h4 := C_norm_fderiv_le hδ (hf.mono hyb) (fun z hz => hM z (hyb hz))
        exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr))
    rw [h1, (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) h2 i).eq_of_nhds]
    calc ‖iteratedFDeriv ℝ i (fun y => fderiv ℂ f y v) x (Fin.init m)‖
        ≤ ‖iteratedFDeriv ℝ i (fun y => fderiv ℂ f y v) x‖ * ∏ j, ‖Fin.init m j‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ (M / δ * ‖v‖ / δ ^ i) * ∏ j, ‖Fin.init m j‖ := by gcongr
      _ = M / δ ^ (i + 1) * ∏ j, ‖m j‖ := by
          rw [Fin.prod_univ_castSucc, ← hv, pow_succ]
          simp only [Fin.init]
          field_simp
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
