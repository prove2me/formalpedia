-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.gI_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:32:28.656626+00:00
-- url     : https://prove2.me/submissions/e34bee53-9b6d-4397-86d2-c01165415efe

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_zj_apply_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_zj_apply_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_zj_apply_rl
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_det_zj
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_entry_le

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
theorem _root_.solution {β c : ℂ} {p : ℕ} {Ψ : G.Mat (p + 1) → V} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hb : ∀ Z ∈ tsupport Ψ, ‖Z‖ ≤ R ∧ δ ≤ ‖G.detM Z‖) {H : G.Mat p} {y : AB p} (hne : gI β c Ψ H y ≠ 0) :
    H ∈ Sset p R (δ / ‖c‖) ∧ (∀ j, ‖(Matrix.of y.1 * Matrix.of H) 0 j‖ ≤ R) ∧
      ∀ i, ‖(Matrix.of H * Matrix.of y.2) i 0‖ ≤ R := by
  have hΨne : Ψ (Zj y.1 y.2 (Matrix.of H) (Matrix.of fun _ _ => c)) ≠ 0 := by
    intro h; apply hne; unfold gI; rw [h, smul_zero]
  obtain ⟨h1, h2⟩ := hb _ (subset_tsupport _ hΨne)
  set Z : G.Mat (p + 1) := Zj y.1 y.2 (Matrix.of H) (Matrix.of fun _ _ => c) with hZ
  have hdet : G.detM Z = G.detM H * c := by
    unfold G.detM
    rw [hZ]
    show (Zj y.1 y.2 (Matrix.of H) (Matrix.of fun _ _ => c)).det = _
    rw [det_zj]
    simp [Matrix.det_unique]
  refine ⟨⟨?_, ?_⟩, fun j => ?_, fun i => ?_⟩
  · refine (pi_norm_le_iff_of_nonneg hR).2 fun i => (pi_norm_le_iff_of_nonneg hR).2 fun j => ?_
    have := entry_le Z (Fin.castAdd 1 i) (Fin.castAdd 1 j)
    rw [hZ, zj_apply_ll] at this
    exact le_trans this h1
  · by_cases hc : c = 0
    · exfalso
      rw [hdet, hc, mul_zero, norm_zero] at h2
      exact absurd h2 (not_le.2 hδ)
    · rw [div_le_iff₀ (norm_pos_iff.2 hc), ← norm_mul, ← hdet]; exact h2
  · have := entry_le Z (Fin.natAdd p 0) (Fin.castAdd 1 j)
    rw [hZ, zj_apply_rl] at this
    exact le_trans this h1
  · have := entry_le Z (Fin.castAdd 1 i) (Fin.natAdd p 0)
    rw [hZ, zj_apply_lr] at this
    exact le_trans this h1
end Formalism.FourierDecayAlt.P.PBJ.Frz
