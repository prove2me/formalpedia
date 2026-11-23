-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:02.303816+00:00
-- url     : https://prove2.me/submissions/513a318a-7f33-46f4-8f90-9c3aa8a74727

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
theorem _root_.solution {f : E → F} {W : ℝ} (p : ℕ) (hw : ∀ x ∈ A, 0 < w x) (hW : ∀ x ∈ A, w x ≤ W)
    (hf : Sym A w (m + p) N K f) : Sym A w m N (K * W ^ p) f := by
  refine ⟨hf.1, fun x hx i hi => ?_⟩
  have hK := A_const_nonneg hw hf hx
  have hwx := hw x hx
  have e : w x ^ (m + (p : ℤ) - (i : ℤ)) = w x ^ (m - (i : ℤ)) * w x ^ p := by
    rw [← zpow_natCast, ← zpow_add₀ hwx.ne']
    congr 1
    ring
  calc ‖iteratedFDeriv ℝ i f x‖ ≤ K * w x ^ (m + (p : ℤ) - (i : ℤ)) := hf.2 x hx i hi
    _ = K * w x ^ p * w x ^ (m - (i : ℤ)) := by rw [e]; ring
    _ ≤ K * W ^ p * w x ^ (m - (i : ℤ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hwx.le (hW x hx) p) hK) (zpow_pos hwx _).le
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
