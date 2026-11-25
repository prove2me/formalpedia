-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpG.hasDerivAt_det_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:06:26.189068+00:00
-- url     : https://prove2.me/submissions/12346557-c046-4a70-979b-796a88ad971f

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_HasFDerivAtOfCurves
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_hasDerivAt
import Theorems.Thm_GlobalTheory_WeilM_IsTilde_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp CompanionTheory.ThKR.Mp.MpG
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.Mp.MpG
theorem _root_.solution {M : ℝ → l → l → ℝ} {X : l → l → ℝ} (h : HasDerivAt M X 0) (h0 : Matrix.of (M 0) = 1) :
    HasDerivAt (fun t => (Matrix.of (M t)).det) (Matrix.of X).trace 0 := by
  have hd : DifferentiableAt ℝ (fun N : l → l → ℝ => (Matrix.of N).det) (M 0) := by
    simp only [Matrix.det_apply', Matrix.of_apply]
    exact DifferentiableAt.fun_sum fun σ _ => (((contDiff_prod (n := 1) (f := fun i (N : l → l → ℝ) => N (σ i) i)
      fun i _ => contDiff_apply_apply ℝ ℝ (σ i) i).differentiable one_ne_zero) _).const_mul _
  have h1 := hd.hasFDerivAt.comp_hasDerivAt 0 h
  have h2 : HasDerivAt (fun t : ℝ => M 0 + t • X) X 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (M 0)
  have h3 := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 h2 (by simp)
  let p := (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • (Matrix.of X).map Polynomial.C)).divX.divX
  have h4 : HasDerivAt (fun t : ℝ => 1 + (Matrix.of X).trace * t + p.eval t * t ^ 2) (Matrix.of X).trace 0 :=
    ((((hasDerivAt_id (0 : ℝ)).const_mul _).const_add 1).fun_add
      ((p.hasDerivAt 0).fun_mul (hasDerivAt_pow 2 0))).congr_deriv (by simp)
  have h5 := h3.unique (h4.congr_of_eventuallyEq (.of_forall fun t => by
    refine Eq.trans ?_ (Matrix.det_one_add_smul t (Matrix.of X))
    rw [← h0]
    rfl))
  exact h5 ▸ h1
end CompanionTheory.ThKR.Mp.MpG
