-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:14:15.801874+00:00
-- url     : https://prove2.me/submissions/6ee0cdd5-ee2c-40a9-9b7e-7156e1555450

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {A : Set E} {w : E → ℝ} {m m₁ m₂ : ℤ} {N : ℕ} {K K₁ K₂ : ℝ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
namespace Sym
theorem _root_.solution (c : F) (hK : 0 ≤ K) (hw : ∀ x ∈ A, 0 < w x) (h : ∀ x ∈ A, ‖c‖ ≤ K * w x ^ m) :
    Sym A w m N K (fun _ : E => c) := by
  refine ⟨contDiff_const, fun x hx i _ => ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [norm_iteratedFDeriv_zero]
    simpa using h x hx
  · rw [iteratedFDeriv_const_of_ne hi.ne']
    simpa using mul_nonneg hK (zpow_pos (hw x hx) _).le
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
