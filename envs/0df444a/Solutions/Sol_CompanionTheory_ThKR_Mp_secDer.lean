-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.secDer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:49.961556+00:00
-- url     : https://prove2.me/submissions/604a990b-fdb0-417d-9d8f-ac86794e2588

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_HasFDerivAtOfCurves
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpG_hasFDerivAt_of_curves
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpG_curve
import Theorems.Thm_CompanionTheory_ThKR_Mp_qd_sum


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
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution : SecDer l := by
  intro E _ _ m m' x₀ h0 hm f
  let L : ((l ⊕ l) → (l ⊕ l) → ℝ) →L[ℝ] L2 l := LinearMap.toContinuousLinearMap
    ((((schwartzToL2 l).restrictScalars ℝ).toLinearMap.comp (qdLin f)).comp (Matrix.ofLinearEquiv ℝ).toLinearMap)
  have hL : ∀ X, L X = schwartzToL2 l (Qd (Matrix.of X) f) := fun X => rfl
  have h1 : HasFDerivAt (fun g : (l ⊕ l) → (l ⊕ l) → ℝ => schwartzToL2 l (sec (Matrix.of g) f)) L (fun a b => m x₀ a b) :=
    MpG.hasFDerivAt_of_curves fun c v c0 hc => MpG.curve (by rw [c0, h0]; rfl) hc f
  have h2 : HasFDerivAt (fun x => fun a b => m x a b)
      (ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b => m' a b) x₀ :=
    hasFDerivAt_pi.2 fun a => hasFDerivAt_pi.2 fun b => hm a b
  refine (h1.comp x₀ h2).congr_fderiv ?_
  ext1 v
  rw [ContinuousLinearMap.comp_apply, hL, ← qd_sum]
  simp only [map_sum, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact ((schwartzToL2 l).restrictScalars ℝ).map_smul _ _
end CompanionTheory.ThKR.Mp
