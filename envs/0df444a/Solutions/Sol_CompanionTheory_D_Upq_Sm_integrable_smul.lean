-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.integrable_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:01:45.710368+00:00
-- url     : https://prove2.me/submissions/2667b247-9c42-4aca-96ea-456e21d1b582

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_isCompact_supp
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
variable {hG : IsMatGroup G}
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ : Mat n → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {f : MG G hG → V} (hf : Continuous f) :
    Integrable (fun g : MG G hG => φ g.mat • f g) haar :=
  ((hφ.comp MG.continuous_mat).smul hf).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_supp hc) fun g hg => by
      change φ g.mat • f g = 0
      rw [image_eq_zero_of_notMem_tsupport hg, zero_smul])
end CompanionTheory.D.Upq.Sm
