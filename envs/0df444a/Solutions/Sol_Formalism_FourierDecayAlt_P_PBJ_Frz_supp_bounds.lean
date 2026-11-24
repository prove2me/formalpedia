-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.supp_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:54.6073+00:00
-- url     : https://prove2.me/submissions/6edc8b63-2c9a-4b36-8508-70572971cf3d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_cont_detM

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
theorem _root_.solution {n : ℕ} {Ψ : G.Mat n → V} (hΨ : KCls Ψ) :
    ∃ R δ : ℝ, 0 ≤ R ∧ 0 < δ ∧ ∀ Z ∈ tsupport Ψ, ‖Z‖ ≤ R ∧ δ ≤ ‖G.detM Z‖ := by
  obtain ⟨_, hc, hdet⟩ := hΨ
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.exists_norm_le
  by_cases hne : (tsupport Ψ).Nonempty
  · obtain ⟨Z₀, hZ₀, hmin⟩ := hc.isCompact.exists_isMinOn hne
      ((continuous_norm.comp (cont_detM n)).continuousOn)
    refine ⟨max R 0, ‖G.detM Z₀‖, le_max_right _ _, norm_pos_iff.2 (hdet Z₀ hZ₀), fun Z hZ => ⟨le_trans (hR Z hZ)
      (le_max_left _ _), hmin hZ⟩⟩
  · refine ⟨0, 1, le_rfl, one_pos, fun Z hZ => absurd ⟨Z, hZ⟩ hne⟩
end Formalism.FourierDecayAlt.P.PBJ.Frz
