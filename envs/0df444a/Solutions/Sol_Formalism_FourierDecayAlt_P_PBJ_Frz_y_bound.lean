-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.y_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:13:33.025716+00:00
-- url     : https://prove2.me/submissions/61a949f3-d0a7-456e-8d09-4adc0f1d4c79

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_gI_ne

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
theorem _root_.solution {β c : ℂ} {p : ℕ} {Ψ : G.Mat (p + 1) → V} {R δ M : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hc : c ≠ 0)
    (hb : ∀ Z ∈ tsupport Ψ, ‖Z‖ ≤ R ∧ δ ≤ ‖G.detM Z‖) (hM0 : 0 ≤ M)
    (hM : ∀ H ∈ Sset p R (δ / ‖c‖), ∀ i j, ‖((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i j‖ ≤ M)
    {H : G.Mat p} {y : AB p} (hne : gI β c Ψ H y ≠ 0) : ‖y‖ ≤ p * R * M := by
  obtain ⟨hS, ha, hbb⟩ := gI_ne hR hδ hb hne
  have hpos : 0 < δ / ‖c‖ := div_pos hδ (norm_pos_iff.2 hc)
  have hdet : IsUnit (Matrix.of H).det :=
    isUnit_iff_ne_zero.2 (norm_pos_iff.1 (lt_of_lt_of_le hpos hS.2))
  have hRM : 0 ≤ (p : ℝ) * R * M := by positivity
  rw [norm_prod_le_iff]
  constructor
  · refine (pi_norm_le_iff_of_nonneg hRM).2 fun i => (pi_norm_le_iff_of_nonneg hRM).2 fun j => ?_
    have e : y.1 i j = ∑ k, (Matrix.of y.1 * Matrix.of H) i k * ((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) k j := by
      rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]; rfl
    rw [e]
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    calc ‖∑ k, (Matrix.of y.1 * Matrix.of H) 0 k * ((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) k j‖
        ≤ ∑ k, ‖(Matrix.of y.1 * Matrix.of H) 0 k * ((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) k j‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k : Fin p, R * M := Finset.sum_le_sum fun k _ => by
          rw [norm_mul]; exact mul_le_mul (ha k) (hM H hS k j) (norm_nonneg _) hR
      _ = p * R * M := by simp; ring
  · refine (pi_norm_le_iff_of_nonneg hRM).2 fun i => (pi_norm_le_iff_of_nonneg hRM).2 fun j => ?_
    have e : y.2 i j = ∑ k, ((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i k * (Matrix.of H * Matrix.of y.2) k j := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]; rfl
    rw [e]
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    calc ‖∑ k, ((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i k * (Matrix.of H * Matrix.of y.2) k 0‖
        ≤ ∑ k, ‖((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i k * (Matrix.of H * Matrix.of y.2) k 0‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k : Fin p, R * M := Finset.sum_le_sum fun k _ => by
          rw [norm_mul, mul_comm R M]; exact mul_le_mul (hM H hS i k) (hbb k) (norm_nonneg _) hM0
      _ = p * R * M := by simp; ring
end Formalism.FourierDecayAlt.P.PBJ.Frz
