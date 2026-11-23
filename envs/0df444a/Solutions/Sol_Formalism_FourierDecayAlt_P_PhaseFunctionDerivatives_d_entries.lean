-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.d_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:36.527053+00:00
-- url     : https://prove2.me/submissions/ba2fe387-9d36-4bce-ba23-cc176e76d5cd

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_blk_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_norm_coord_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
theorem _root_.solution {m : ℕ} (t σ ρ₁ : ℂ) (ρ' : Fin m → ℂ) (x : UT (m + 1) → ℂ) (B : Fin (m + 1) → ℂ) (T : ℝ)
    (hT : 0 ≤ T) (h : ∀ i j, ‖Mcoord t (strictUpper x) B (Fin.cons ρ₁ ρ') σ i j‖ ≤ T) :
    (∀ i j, ‖strictUpper x i j‖ ≤ T) ∧ (∀ i, ‖B i‖ ≤ T) ∧ ‖ρ₁‖ ≤ T ∧ (∀ k, ‖ρ' k‖ ≤ T) ∧ ‖σ‖ ≤ T := by
  obtain ⟨Z, hZd⟩ : ∃ Z : Mat (m + 1 + 1), Z = Mcoord t (strictUpper x) B (Fin.cons ρ₁ ρ') σ := ⟨_, rfl⟩
  have hZ : ‖Z‖ ≤ T := by
    rw [pi_norm_le_iff_of_nonneg hT]
    intro i
    rw [pi_norm_le_iff_of_nonneg hT]
    intro j
    rw [hZd]
    exact h i j
  have hco := (G7.norm_coord_le t σ x B (Fin.cons ρ₁ ρ') Z hZd).trans hZ
  have h1 : ‖(Fin.cons ρ₁ ρ' : Fin (m + 1) → ℂ)‖ ≤ T := (norm_fst_le _).trans hco
  have h2 : ‖x‖ ≤ T := ((norm_fst_le _).trans (norm_snd_le _)).trans hco
  have h3 : ‖B‖ ≤ T := ((norm_snd_le _).trans (norm_snd_le _)).trans hco
  refine ⟨fun i j => ?_, fun i => (norm_le_pi_norm B i).trans h3, ?_, fun k => ?_, ?_⟩
  · by_cases hij : i < j
    · simp only [strictUpper, Matrix.of_apply, hij, dif_pos]
      exact (norm_le_pi_norm x _).trans h2
    · simp only [strictUpper, Matrix.of_apply, hij, dif_neg, not_false_iff, norm_zero]
      exact hT
  · simpa using (norm_le_pi_norm (Fin.cons ρ₁ ρ' : Fin (m + 1) → ℂ) 0).trans h1
  · simpa using (norm_le_pi_norm (Fin.cons ρ₁ ρ' : Fin (m + 1) → ℂ) k.succ).trans h1
  · have := h (Fin.last (m + 1)) (Fin.last (m + 1))
    rwa [Mcoord, G2.blk_ll] at this
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
