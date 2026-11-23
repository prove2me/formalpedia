-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_nsq_sym
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:14.213319+00:00
-- url     : https://prove2.me/submissions/c4efc65c-886e-45a1-a1ee-da3147f064ab

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_clm
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_wt_pos

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
theorem _root_.solution (d N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ Sym (Set.univ : Set (Fin d → ℂ)) (wt 1) 2 N K (D_nsq d) := by
  have hw : ∀ x ∈ (Set.univ : Set (Fin d → ℂ)), 0 < wt (1 : ℝ) x := fun x _ => D_wt_pos one_pos x
  let Lr : Fin d → ((Fin d → ℂ) →L[ℝ] ℝ) := fun k =>
    Complex.reCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) k)
  let Li : Fin d → ((Fin d → ℂ) →L[ℝ] ℝ) := fun k =>
    Complex.imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℂ) k)
  have h1 : ∀ k ∈ (Finset.univ : Finset (Fin d)), Sym (Set.univ : Set (Fin d → ℂ)) (wt 1) 2 N
      (2 ^ N * ‖Lr k‖ * ‖Lr k‖ + 2 ^ N * ‖Li k‖ * ‖Li k‖) (fun x => Lr k x * Lr k x + Li k x * Li k x) := by
    intro k _
    exact (Sym.mul hw (Sym.clm (Lr k) one_pos) (Sym.clm (Lr k) one_pos)).add
      (Sym.mul hw (Sym.clm (Li k) one_pos) (Sym.clm (Li k) one_pos))
  refine ⟨∑ k : Fin d, (2 ^ N * ‖Lr k‖ * ‖Lr k‖ + 2 ^ N * ‖Li k‖ * ‖Li k‖), by positivity, ?_⟩
  have h2 := Sym.sum Finset.univ h1
  convert h2 using 2 with x
  unfold D_nsq
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Lr, Li, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Complex.reCLM_apply,
    Complex.imCLM_apply]
  rw [Complex.sq_norm, Complex.normSq_apply]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
