-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagGramRestriction.mulV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:08:06.084444+00:00
-- url     : https://prove2.me/submissions/2652c2b5-1e7a-49d1-9579-d84f02aa4cfd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_col_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_col_V_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_mat_ext_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_map_frame
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_col_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagGramRestriction
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FlagGramRestriction
theorem _root_.solution {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ : B.Mat k r} (hγ : IsUnit γ.det)
    {h : B.Mat k r} (hs : h ∈ Sset k r z) (hs' : γ⁻¹ * h * γ ∈ Sset k r z') :
    h * gnB k r z z' γ = gnB k r z z' γ * PhiH k r z z' γ h := by
  have hU := (unipotent_map_frame k r z hstd.2.1).1 h hs
  have hU' := (unipotent_map_frame k r z' hstd.2.2).1 _ hs'
  apply mat_ext_col
  intro j
  rw [col_mul, col_V_mul, Fintype.sum_sum_type]
  cases j with
  | inl b =>
    simp only [PhiH, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero]
    exact hU.1 b
  | inr b =>
    simp only [PhiH, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_smul,
      Finset.sum_const_zero, zero_add]
    show h *ᵥ (γ *ᵥ fvec k r z' b) = ∑ c, C2.uMap k r z' (γ⁻¹ * h * γ) c b • (γ *ᵥ fvec k r z' c)
    have e : h * γ = γ * (γ⁻¹ * h * γ) := by
      simp only [Matrix.mul_assoc]; rw [Matrix.mul_nonsing_inv_cancel_left _ _ hγ]
    rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, hU'.1 b, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
end Formalism.FourierDecayAlt.P.FlagGramRestriction
