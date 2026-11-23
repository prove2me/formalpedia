-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.norm_le_of_hs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:46.132697+00:00
-- url     : https://prove2.me/submissions/93840425-e14b-42a1-a671-1d1e4626cf64

import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingBump

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace CompanionTheory.D.gk.admitted.Gard
theorem _root_.solution {y : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (hr : 0 ≤ r) (h : hs y ≤ r ^ 2) : ‖y‖ ≤ r := by
  rw [Matrix.norm_le_iff hr]
  intro i j
  have h1 : ‖y i j‖ ^ 2 ≤ ∑ j, ‖y i j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖y i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ j, ‖y i j‖ ^ 2 ≤ hs y :=
    Finset.single_le_sum (f := fun i => ∑ j, ‖y i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero).1 (h1.trans (h2.trans h))
end CompanionTheory.D.gk.admitted.Gard
