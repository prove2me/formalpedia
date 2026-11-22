-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.const_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:24.992086+00:00
-- url     : https://prove2.me/submissions/4160acbd-1e76-42aa-8155-d301fb67bde7

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_A_cda

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
theorem _root_.solution {f : E → F} (c : ℝ) (hf : Sym A w m N K f) :
    Sym A w m N (|c| * K) (fun x => c • f x) := by
  refine ⟨hf.1.const_smul c, fun x hx i hi => ?_⟩
  have h1 : iteratedFDeriv ℝ i (fun x => c • f x) x = c • iteratedFDeriv ℝ i f x :=
    iteratedFDeriv_const_smul_apply (A_cda hf.1 hi x)
  rw [h1, norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf.2 x hx i hi) (abs_nonneg c)
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
