-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.bound_tag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:43:57.143573+00:00
-- url     : https://prove2.me/submissions/8066356c-581e-413c-a159-993cac5c00a1

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_of_tags

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {F : Mat k r → E} {A c : ℝ} {m : ℕ} (h : CCle A m F c) (w : List (Bool × Mat k r))
    (ht : LRt (w.map Prod.fst)) (hu : ∀ x ∈ w, unitLie k r x.2) (hl : w.length ≤ m) :
    ∀ g ∈ GV k r, gN g ^ A * ‖W w F g‖ ≤ c := by
  intro g hg
  obtain ⟨a, b, hab⟩ := ht
  obtain ⟨u, v, _, rfl⟩ := of_tags w a b hab
  rw [← dLR_eq]
  have hu' : ∀ X ∈ u, unitLie k r X := fun X hX => hu (true, X) (by simp [lr, hX])
  have hv' : ∀ X ∈ v, unitLie k r X := fun X hX => hu (false, X) (by simp [lr, hX])
  have hl' : u.length + v.length ≤ m := by
    rw [length_lr] at hl
    exact hl
  unfold CCle at h
  exact h.2 u v hu' hv' hl' g hg
end Formalism.FourierDecayAlt.P.B4
