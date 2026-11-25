-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.integrable_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:16:21.7988+00:00
-- url     : https://prove2.me/submissions/4350faf4-cc65-4f7b-867e-c665c2296b01

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_decay0
import Theorems.Thm_Formalism_FourierDecayAlt_P_top_cells


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBJ Formalism.FourierDecayAlt.P.PBJ.Frz
open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.PBJ.Frz
theorem _root_.solution [CompleteSpace V] (β c : ℂ) {p : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (hd : ∀ i, d i ≠ 0) {Ψ : G.Mat (p + 1) → V} (hΨ : KCls Ψ) :
    Integrable (fun η : XiH p 1 σ => psiH β σ η • Ψ (ZjH σ d η (fun _ _ => c))) (muXiH p 1 σ) := by
  set E : ℝ := 10 * ((p + 1 : ℕ) : ℝ) ^ 3 + 1 with hEdef
  have hE : 0 ≤ E := by positivity
  obtain ⟨Cst, hC⟩ := Formalism.FourierDecayAlt.P.top_cells p 1 β σ d hd le_rfl 0 (fun _ => E) (by
    intro i _
    have hn : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := by positivity
    rw [lt_div_iff₀ (by positivity)]
    nlinarith)
  obtain ⟨K, hK⟩ := decay0 hΨ E hE
  exact (hC V Ψ K hK).1 (fun _ _ => c)
end Formalism.FourierDecayAlt.P.PBJ.Frz
