-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.inv_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:36:23.585834+00:00
-- url     : https://prove2.me/submissions/049519ca-e3ca-4fd8-91d9-373ebecefc5c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_cont_detM
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_isCompact_Sset

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
theorem _root_.solution (p : ℕ) (R δ' : ℝ) (hδ : 0 < δ') : ∃ M : ℝ, 0 ≤ M ∧
    ∀ H ∈ Sset p R δ', ∀ i j, ‖((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i j‖ ≤ M := by
  have hcont : ∀ i j, ContinuousOn (fun H : G.Mat p => ((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i j)
      (Sset p R δ') := by
    intro i j
    have e : (fun H : G.Mat p => ((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i j) =
        fun H => (G.detM H)⁻¹ * (Matrix.of H).adjugate i j := by
      funext H
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
      rfl
    rw [e]
    refine ContinuousOn.mul ?_ ((Continuous.matrix_adjugate continuous_id).matrix_elem i j).continuousOn
    refine (cont_detM p).continuousOn.inv₀ fun H hH => ?_
    exact norm_pos_iff.1 (lt_of_lt_of_le hδ hH.2)
  have hb : ∀ i j, ∃ C : ℝ, ∀ H ∈ Sset p R δ', ‖((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i j‖ ≤ C :=
    fun i j => (isCompact_Sset p R δ').exists_bound_of_continuousOn (hcont i j)
  choose C hC using hb
  refine ⟨∑ i, ∑ j, max (C i j) 0, by positivity, fun H hH i j => ?_⟩
  refine le_trans (hC i j H hH) (le_trans (le_max_left _ 0) ?_)
  have h1 : max (C i j) 0 ≤ ∑ j', max (C i j') 0 :=
    Finset.single_le_sum (f := fun j' => max (C i j') 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ j)
  have h2 : ∑ j', max (C i j') 0 ≤ ∑ i', ∑ j', max (C i' j') 0 :=
    Finset.single_le_sum (f := fun i' => ∑ j', max (C i' j') 0)
      (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ i)
  exact le_trans h1 h2
end Formalism.FourierDecayAlt.P.PBJ.Frz
