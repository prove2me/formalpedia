-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.continuous_iter_partial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:44.253059+00:00
-- url     : https://prove2.me/submissions/f7177e75-fb96-46fc-b63c-b5293a119e62

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
variable {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace CompanionTheory.D.gk.admitted.Gard
theorem _root_.solution (Φ : P × Q → E) (hΦ : ContDiff ℝ ∞ Φ) (k : ℕ) :
    Continuous fun p : P × Q => iteratedFDeriv ℝ k (fun y => Φ (y, p.2)) p.1 := by
  have h : (fun p : P × Q => iteratedFDeriv ℝ k (fun y => Φ (y, p.2)) p.1) =
      fun p => (iteratedFDeriv ℝ k Φ p).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ P Q) := by
    funext p
    have e : (fun y => Φ (y, p.2)) =
        (fun z => Φ (z + (0, p.2))) ∘ (ContinuousLinearMap.inl ℝ P Q) := by
      funext y; simp
    have hs : ContDiff ℝ ∞ (fun z : P × Q => Φ (z + (0, p.2))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hs _ (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    simp
  rw [h]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin k => ContinuousLinearMap.inl ℝ P Q)).continuous.comp
      (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
end CompanionTheory.D.gk.admitted.Gard
