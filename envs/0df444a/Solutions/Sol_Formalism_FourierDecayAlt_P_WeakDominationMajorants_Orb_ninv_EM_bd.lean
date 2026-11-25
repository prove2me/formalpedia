-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.ninv_EM_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:54:09.169829+00:00
-- url     : https://prove2.me/submissions/c41c798c-d956-4f94-8bd3-9000e329c1bc

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_norm_inv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_n_mem_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_n_rowEs
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_n_rowM
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_sg_eI
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_one_le_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_orbit_constant_five_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_orbit_constant_ten_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_pow_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_Linv_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_Nstar
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_rowM_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_Es_of_gt
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_E_of_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_sg_M
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix
open Matrix
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationMajorants Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {k r : ℕ}
variable {Γ δ : ℝ} {g n n' : Mat k r}
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
theorem _root_.solution (hΓ : 1 ≤ Γ) (hδ : 0 < δ) (hg : g ∈ GV k r) (hgΓ : gN g ≤ Γ) (hld : ∀ b, δ ≤ ‖ld (Zm g) b‖)
    (hdet : δ ≤ ‖(Zm g).det‖) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r)
    (i l : Fin (2 * r + k + 1)) (hl : l.val ≤ r + k) :
    ‖n⁻¹ i l‖ ≤ c11 r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1) := by
  set X := gN (n⁻¹ * g * n')
  have hX : 1 ≤ X := one_le_X hg hn hn'
  have hXp : 1 ≤ X ^ (2 * r + 1) := one_le_pow₀ hX
  have := orbit_constant_five_nonneg (r := r) hΓ hδ; have := orbit_constant_ten_nonneg (r := r) hΓ hδ
  have hc : c11 r Γ δ * X ^ (2 * r + 1) = X ^ (2 * r + 1) + c5 r Γ δ * X ^ (2 * r + 1) +
      c10 r Γ δ * X ^ (2 * r + 1) := by unfold c11; ring
  rw [norm_inv_apply (n_mem_G hn), hc]
  have hc5 : c5 r Γ δ * X ^ (2 * r) ≤ c5 r Γ δ * X ^ (2 * r + 1) :=
    mul_le_mul_of_nonneg_left (pow_mono hX (by omega)) (orbit_constant_five_nonneg hΓ hδ)
  have nn1 : 0 ≤ c5 r Γ δ * X ^ (2 * r + 1) := by positivity
  have nn2 : 0 ≤ c10 r Γ δ * X ^ (2 * r + 1) := by positivity
  by_cases hlE : l.val < r
  · obtain ⟨b, rfl⟩ := E_of_lt l hlE
    rw [sg_eI]
    by_cases hi : (sg k r i).val ≤ r + k
    · rw [n_rowEs hn _ _ (by simp [esI]; omega) hi, norm_zero]; positivity
    · obtain ⟨a', ha'⟩ := Es_of_gt (sg k r i) (by omega)
      rw [ha', Nstar hn]
      have := Linv_bd hΓ hδ hg hgΓ hld hdet hn hn' b a'
      linarith
  · rw [sg_M l (by omega) hl]
    by_cases hi : (sg k r i).val ≤ r + k
    · rw [n_rowM hn l _ (by omega) hi]
      split_ifs <;> simp <;> linarith
    · obtain ⟨a', ha'⟩ := Es_of_gt (sg k r i) (by omega)
      rw [ha']
      have := rowM_bd hΓ hδ hg hgΓ hld hdet hn hn' l (by omega) hl a'
      linarith
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
