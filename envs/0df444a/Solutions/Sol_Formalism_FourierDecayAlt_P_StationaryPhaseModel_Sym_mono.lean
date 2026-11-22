-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:06:20.16785+00:00
-- url     : https://prove2.me/submissions/70cb31ec-6dde-4d83-ba7f-1024270dc9ce

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
theorem _root_.solution {f : E → F} {N' : ℕ} {K' : ℝ} (hw : ∀ x ∈ A, 0 < w x) (h : Sym A w m N K f) (hN : N' ≤ N)
    (hK : K ≤ K') : Sym A w m N' K' f := by
  refine ⟨h.1.of_le (by exact_mod_cast hN), fun x hx i hi => ?_⟩
  refine (h.2 x hx i (hi.trans hN)).trans ?_
  exact mul_le_mul_of_nonneg_right hK (zpow_pos (hw x hx) _).le
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
