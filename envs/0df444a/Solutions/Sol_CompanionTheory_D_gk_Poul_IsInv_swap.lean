-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.IsInv.swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:36:13.242618+00:00
-- url     : https://prove2.me/submissions/14345480-9126-477b-b1e2-9e0b2dac1436

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.Poul
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {hG : IsMatGroup G}
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {σ : Mat n → (H →L[ℂ] H)} {σ' : Mat n → (H' →L[ℂ] H')}
variable {ι ι' : Type} [Fintype ι] [Fintype ι'] {W : ι → List (Mat n)} {W' : ι' → List (Mat n)} {C : ℝ}
  {B : H → H' → ℂ}
omit [CompleteSpace H] [CompleteSpace H']
namespace CompanionTheory.D.gk.Poul
namespace IsInv
theorem _root_.solution (hB : IsInv G σ σ' W W' C B) : IsInv G σ' σ W' W C fun y x => star (B x y) where
  add_left y y' x hy hy' hx := by rw [hB.add_right x y y' hx hy hy', star_add]
  smul_left a y x hy hx := by rw [hB.smul_right a x y hx hy, star_mul', star_star]
  add_right y x x' hy hx hx' := by rw [hB.add_left x x' y hx hx' hy, star_add]
  smul_right a y x hy hx := by rw [hB.smul_left a x y hx hy, star_mul']
  inv g hg y x hy hx := by rw [hB.inv g hg x y hx hy]
  bd y x hy hx := by rw [norm_star, mul_right_comm]; exact hB.bd x y hx hy
end IsInv
end CompanionTheory.D.gk.Poul
