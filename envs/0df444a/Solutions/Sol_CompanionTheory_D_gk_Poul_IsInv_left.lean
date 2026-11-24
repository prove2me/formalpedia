-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.IsInv.left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:36:19.708292+00:00
-- url     : https://prove2.me/submissions/4e299e6b-fcc6-466a-8944-3f8aee78fdc5

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add


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
theorem _root_.solution (hB : IsInv G σ σ' W W' C B) {y : H'} (hy : IsSm G σ' y) :
    IsSmForm G σ W (C * ∑ j, ‖dsW σ' (W' j) y‖) fun x => B x y where
  add x x' hx hx' := hB.add_left x x' y hx hx' hy
  smul a x hx := hB.smul_left a x y hx hy
  bd x hx := by rw [mul_right_comm]; exact hB.bd x y hx hy
end IsInv
end CompanionTheory.D.gk.Poul
