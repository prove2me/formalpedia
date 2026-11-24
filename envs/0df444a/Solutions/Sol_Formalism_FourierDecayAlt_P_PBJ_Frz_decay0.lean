-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.decay0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:37.716053+00:00
-- url     : https://prove2.me/submissions/b35c8802-dae6-4696-837e-5613cc951cc1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize

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
theorem _root_.solution {n : ℕ} {Ψ : G.Mat n → V} (hΨ : KCls Ψ) (E : ℝ) (hE : 0 ≤ E) :
    ∃ K : ℝ, DecayAll 0 (fun _ => E) K Ψ := by
  obtain ⟨hs, hc, _⟩ := hΨ
  have hcont : Continuous Ψ := hs.continuous
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hc
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.exists_norm_le
  set R' := max R 0 with hR'
  set M' := max M 0 with hM'
  refine ⟨M' * (1 + R') ^ E, ?_, ?_⟩
  · rw [Nat.cast_zero]; exact contDiff_zero.2 hcont
  · intro i hi Z
    have hi0 : i = 0 := Nat.le_zero.1 hi
    subst hi0
    rw [norm_iteratedFDeriv_zero]
    have h1 : (0 : ℝ) < 1 + ‖Z‖ := by positivity
    have hpow : (1 + ‖Z‖) ^ E * (1 + ‖Z‖) ^ (-E) = 1 := by
      rw [Real.rpow_neg h1.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos h1 E).ne']
    by_cases hZ : Z ∈ tsupport Ψ
    · have hZR : ‖Z‖ ≤ R' := le_trans (hR Z hZ) (le_max_left _ _)
      have hle : (1 + ‖Z‖) ^ E ≤ (1 + R') ^ E := Real.rpow_le_rpow h1.le (by linarith) hE
      have hneg : 0 ≤ (1 + ‖Z‖) ^ (-E) := (Real.rpow_pos_of_pos h1 _).le
      calc ‖Ψ Z‖ ≤ M' := le_trans (hM Z) (le_max_left _ _)
        _ = M' * ((1 + ‖Z‖) ^ E * (1 + ‖Z‖) ^ (-E)) := by rw [hpow, mul_one]
        _ ≤ M' * ((1 + R') ^ E * (1 + ‖Z‖) ^ (-E)) := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          exact mul_le_mul_of_nonneg_right hle hneg
        _ = M' * (1 + R') ^ E * (1 + ‖Z‖) ^ (-E) := by ring
    · rw [image_eq_zero_of_notMem_tsupport hZ, norm_zero]
      have : 0 ≤ (1 + R') ^ E := Real.rpow_nonneg (by positivity) E
      have : 0 ≤ (1 + ‖Z‖) ^ (-E) := (Real.rpow_pos_of_pos h1 _).le
      have : 0 ≤ M' := le_max_right _ _
      positivity
end Formalism.FourierDecayAlt.P.PBJ.Frz
