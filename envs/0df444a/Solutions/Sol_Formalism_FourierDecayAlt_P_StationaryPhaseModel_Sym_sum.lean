-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:22.538472+00:00
-- url     : https://prove2.me/submissions/a7df7bce-d22f-4308-b027-357b1172b995

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
theorem _root_.solution {ι : Type*} (s : Finset ι) {f : ι → E → F} {Kl : ι → ℝ}
    (h : ∀ l ∈ s, Sym A w m N (Kl l) (f l)) : Sym A w m N (∑ l ∈ s, Kl l) (fun x => ∑ l ∈ s, f l x) := by
  refine ⟨ContDiff.sum fun l hl => (h l hl).1, fun x hx i hi => ?_⟩
  have h1 : iteratedFDeriv ℝ i (fun x => ∑ l ∈ s, f l x) = ∑ l ∈ s, iteratedFDeriv ℝ i (f l) :=
    iteratedFDeriv_sum fun l hl => (h l hl).1.of_le (by exact_mod_cast hi)
  rw [h1, Finset.sum_apply, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => (h l hl).2 x hx i hi)
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
