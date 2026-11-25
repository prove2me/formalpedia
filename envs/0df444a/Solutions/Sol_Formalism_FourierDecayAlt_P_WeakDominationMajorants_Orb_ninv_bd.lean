-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.ninv_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:17:43.916637+00:00
-- url     : https://prove2.me/submissions/685bd31a-cc84-49df-b310-1234bf073376

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_sum_split_Es
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_one_le_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_cPg_nn
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_orbit_constant_nine_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_orbit_constant_eleven_ge_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_det_Zx
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_Pm_Es
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_unit_of_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_Pmg_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_Q_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_Es_of_gt
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_ninv_EM_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
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
    (i l : Fin (2 * r + k + 1)) : ‖n⁻¹ i l‖ ≤ c13 k r Γ δ * gN (n⁻¹ * g * n') ^ (2 * r + 1) := by
  set X := gN (n⁻¹ * g * n')
  have hX : 1 ≤ X := one_le_X hg hn hn'
  have := orbit_constant_nine_nonneg (r := r) hΓ hδ; have := orbit_constant_eleven_ge_one (r := r) hΓ hδ; have := cPg_nn (r := r) hΓ hδ
  have hXp : 0 ≤ X ^ (2 * r + 1) := by positivity
  by_cases hl : l.val ≤ r + k
  · have h := ninv_EM_bd hΓ hδ hg hgΓ hld hdet hn hn' i l hl
    refine h.trans ?_
    unfold c13
    have : 0 ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (c11 r Γ δ * cPg r Γ δ) := by positivity
    nlinarith
  · obtain ⟨a, rfl⟩ := Es_of_gt l (by omega)
    have hx : IsUnit (Zm (n⁻¹ * g * n')).det := by rw [det_Zx hn hn']; exact unit_of_det hδ hdet
    have hk := congrFun (congrFun (key hδ hdet hn hn') i) a
    rw [Matrix.mul_apply, sum_split_Es] at hk
    simp only [Pm_Es g (unit_of_det hδ hdet), mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at hk
    have e : n⁻¹ i (esI k r a) = (Pm (n⁻¹ * g * n') * Lm n) i a -
        ∑ l, (if l.val ≤ r + k then n⁻¹ i l * Pm g l a else 0) := by rw [← hk]; ring
    rw [e]
    have h1 := Q_bd hΓ hδ hg hgΓ hld hdet hn hn' i a
    have h2 : ‖∑ l, (if l.val ≤ r + k then n⁻¹ i l * Pm g l a else 0)‖ ≤
        ((2 * r + k + 1 : ℕ) : ℝ) * (c11 r Γ δ * X ^ (2 * r + 1) * cPg r Γ δ) := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ l ∈ Finset.univ, ‖(if l.val ≤ r + k then n⁻¹ i l * Pm g l a else 0)‖ ≤
          c11 r Γ δ * X ^ (2 * r + 1) * cPg r Γ δ := by
        intro l _
        split_ifs with hl'
        · rw [norm_mul]
          exact mul_le_mul (ninv_EM_bd hΓ hδ hg hgΓ hld hdet hn hn' i l hl') (Pmg_bd hΓ hδ hgΓ hdet l a)
            (norm_nonneg _) (by positivity)
        · simp; positivity
      refine (Finset.sum_le_card_nsmul _ _ _ this).trans ?_
      simp
    calc ‖(Pm (n⁻¹ * g * n') * Lm n) i a - ∑ l, (if l.val ≤ r + k then n⁻¹ i l * Pm g l a else 0)‖
        ≤ ‖(Pm (n⁻¹ * g * n') * Lm n) i a‖ + ‖∑ l, (if l.val ≤ r + k then n⁻¹ i l * Pm g l a else 0)‖ :=
          norm_sub_le _ _
      _ ≤ c9 r Γ δ * X ^ (2 * r + 1) + ((2 * r + k + 1 : ℕ) : ℝ) * (c11 r Γ δ * X ^ (2 * r + 1) * cPg r Γ δ) :=
          add_le_add h1 h2
      _ ≤ c13 k r Γ δ * X ^ (2 * r + 1) := by
          unfold c13
          have : 0 ≤ c11 r Γ δ * X ^ (2 * r + 1) := by positivity
          nlinarith
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
