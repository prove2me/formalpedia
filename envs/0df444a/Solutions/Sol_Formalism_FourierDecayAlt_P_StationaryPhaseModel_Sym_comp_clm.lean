-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.comp_clm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:17.989799+00:00
-- url     : https://prove2.me/submissions/1086edbf-0d87-498b-9660-bd4036448f81

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
theorem _root_.solution {f : E → F} (T : F →L[ℝ] G) (hf : Sym A w m N K f) :
    Sym A w m N (‖T‖ * K) (fun x => T (f x)) := by
  refine ⟨T.contDiff.comp hf.1, fun x hx i hi => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ i (fun x => T (f x)) x‖ ≤ ‖T‖ * ‖iteratedFDeriv ℝ i f x‖ :=
    T.norm_iteratedFDeriv_comp_left (A_cda hf.1 hi x) le_rfl
  rw [mul_assoc]
  exact h1.trans (mul_le_mul_of_nonneg_left (hf.2 x hx i hi) (norm_nonneg T))
end Sym
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
