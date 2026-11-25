-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.dsW_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:52.867331+00:00
-- url     : https://prove2.me/submissions/e1580fcf-5348-4b3a-8f97-81470f1ea48c

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_cons
import Theorems.Thm_CompanionTheory_D_Upq_Sm_hasDerivAt_B


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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat n → (H →L[ℂ] H)}
namespace CompanionTheory.D.gk.Poul
theorem _root_.solution (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {φ : Mat n → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) {W : List (Mat n)} (hW : LieW G W) :
    dsW σ W (avg hG φ σ v) = ∫ g : MG G hG, φ g.mat • dsW σ W (σ g.mat v) ∂haar := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : LieW G W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    rw [dsW_cons, ih hW']
    exact (hasDerivAt_B h hv (hW X List.mem_cons_self) hW' hφ hc).deriv
end CompanionTheory.D.gk.Poul
