-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.raise
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:18.451953+00:00
-- url     : https://prove2.me/submissions/83fa1499-7276-4937-ae66-27744135b0ef

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
theorem _root_.solution {f : E → F} {w₀ : ℝ} (p : ℕ) (hw₀ : 0 < w₀) (hW : ∀ x ∈ A, w₀ ≤ w x)
    (hf : Sym A w m N K f) : Sym A w (m + p) N (K / w₀ ^ p) f := by
  have hw : ∀ x ∈ A, 0 < w x := fun x hx => hw₀.trans_le (hW x hx)
  refine ⟨hf.1, fun x hx i hi => ?_⟩
  have hK := A_const_nonneg hw hf hx
  have hwx := hw x hx
  have e : w x ^ (m + (p : ℤ) - (i : ℤ)) = w x ^ (m - (i : ℤ)) * w x ^ p := by
    rw [← zpow_natCast, ← zpow_add₀ hwx.ne']
    congr 1
    ring
  have h1 : 1 ≤ w x ^ p / w₀ ^ p := by
    rw [le_div_iff₀ (pow_pos hw₀ p), one_mul]
    exact pow_le_pow_left₀ hw₀.le (hW x hx) p
  calc ‖iteratedFDeriv ℝ i f x‖ ≤ K * w x ^ (m - (i : ℤ)) := hf.2 x hx i hi
    _ = K * w x ^ (m - (i : ℤ)) * 1 := by ring
    _ ≤ K * w x ^ (m - (i : ℤ)) * (w x ^ p / w₀ ^ p) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hK (zpow_pos hwx _).le)
    _ = K / w₀ ^ p * w x ^ (m + (p : ℤ) - (i : ℤ)) := by rw [e]; ring
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
