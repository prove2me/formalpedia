-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.rowM_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:30:52.250942+00:00
-- url     : https://prove2.me/submissions/0dc4d0a9-b0a2-49ba-848d-79ca1da74941

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_closedN
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_n_rowM
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_sum_split_Es
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_det_Lm
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_det_Zx
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_Pm_Es
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_unit_of_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_closedN
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
theorem _root_.solution (hδ : 0 < δ) (hdet : δ ≤ ‖(Zm g).det‖) (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r)
    (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) (a : Fin r) :
    n j (esI k r a) = (Pm g * (Lm n)⁻¹) j a - Pm (n⁻¹ * g * n') j a := by
  set Q := Pm (n⁻¹ * g * n') * Lm n with hQ
  set Rm : Matrix (Fin (2 * r + k + 1)) (Fin r) ℂ := Matrix.of fun i a => n i (esI k r a)
  have hu : IsUnit n.det := closedN.unit n hn
  have hPg : Pm g = n * Q := by
    rw [hQ, ← key hδ hdet hn hn', ← Matrix.mul_assoc, Matrix.mul_nonsing_inv n hu, Matrix.one_mul]
  have hx : IsUnit (Zm (n⁻¹ * g * n')).det := by rw [det_Zx hn hn']; exact unit_of_det hδ hdet
  have hrow : ∀ c, Pm g j c = Q j c + (Rm * Lm n) j c := by
    intro c
    rw [hPg, Matrix.mul_apply, sum_split_Es]
    congr 1
    · rw [Finset.sum_eq_single j]
      · rw [if_pos hj2, n_rowM hn j j hj1 hj2, if_pos rfl, one_mul]
      · intro l _ hlj
        split_ifs with hl
        · rw [n_rowM hn j l hj1 hl, if_neg (Ne.symm hlj), zero_mul]
        · rfl
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [Matrix.mul_apply, Rm, Matrix.of_apply]
      refine Finset.sum_congr rfl fun a' _ => ?_
      congr 1
      rw [hQ, Matrix.mul_apply]
      simp only [Pm_Es _ hx, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hLL : Lm n * (Lm n)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [det_Lm hn]; exact isUnit_one)
  have e1 : (Pm g * (Lm n)⁻¹) j a = (Q * (Lm n)⁻¹) j a + (Rm * Lm n * (Lm n)⁻¹) j a := by
    simp only [Matrix.mul_apply (M := Pm g), hrow, add_mul, Finset.sum_add_distrib]
    rfl
  rw [e1, hQ, Matrix.mul_assoc (Pm (n⁻¹ * g * n')) (Lm n), hLL, Matrix.mul_one,
    Matrix.mul_assoc Rm (Lm n), hLL, Matrix.mul_one]
  simp [Rm]
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
