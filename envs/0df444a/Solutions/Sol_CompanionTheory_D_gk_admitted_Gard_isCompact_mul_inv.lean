-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.isCompact_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:43.163975+00:00
-- url     : https://prove2.me/submissions/2de95a3a-3bc8-4fb3-9f5a-dee26c3cb5a7

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
theorem _root_.solution {A S : Set (Matrix (Fin n) (Fin n) ℂ)} (hA : IsCompact A) (hS : IsCompact S)
    (hd : ∀ B ∈ S, B.det ≠ 0) :
    IsCompact ((fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2⁻¹) '' (A ×ˢ S)) := by
  refine (hA.prod hS).image_of_continuousOn fun p hp => ?_
  have h1 : ContinuousAt (Inv.inv : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) p.2 := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hd _ hp.2)
  exact (continuousAt_fst.mul (h1.comp continuousAt_snd)).continuousWithinAt
end CompanionTheory.D.gk.admitted.Gard
