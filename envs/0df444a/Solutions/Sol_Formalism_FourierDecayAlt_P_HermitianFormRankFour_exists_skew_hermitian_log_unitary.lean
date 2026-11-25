-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.exists_skew_hermitian_log_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:45:16.667329+00:00
-- url     : https://prove2.me/submissions/717a6eb7-f540-4796-afc4-2db186428be3

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_exists_theta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
open Formalism.FourierDecayAlt.P.HermitianFormRankFour
open scoped Matrix.Norms.L2Operator
namespace Formalism.FourierDecayAlt.P.HermitianFormRankFour
theorem _root_.solution {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (hA : Aᴴ * A = 1) :
    ∃ B : Matrix (Fin k) (Fin k) ℂ, Bᴴ = -B ∧ NormedSpace.exp B = A := by
  obtain ⟨θ, hθ⟩ := exists_theta A
  have hA' : A * Aᴴ = 1 := mul_eq_one_comm.1 hA
  set c : ℂ := Complex.exp (-(θ * Complex.I)) with hc
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hcc : star c * c = 1 := by
    rw [hc, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  have hu : c • A ∈ unitary (Matrix (Fin k) (Fin k) ℂ) := by
    rw [Unitary.mem_iff, star_smul, Matrix.star_eq_conjTranspose]
    constructor
    · rw [smul_mul_smul_comm, hA, hcc, one_smul]
    · rw [smul_mul_smul_comm, hA', mul_comm, hcc, one_smul]
  have hsp : (-1 : ℂ) ∉ spectrum ℂ (c • A) := by
    intro h
    apply hθ
    have h2 := (spectrum.smul_mem_smul_iff (a := A) (s := -Complex.exp (θ * Complex.I)) (r := Units.mk0 c hc0)).1
    apply h2
    have e1 : (Units.mk0 c hc0) • (-Complex.exp (θ * Complex.I)) = (-1 : ℂ) := by
      show c * (-Complex.exp (θ * Complex.I)) = -1
      rw [hc, mul_neg, ← Complex.exp_add]
      simp
    rw [e1]
    exact h
  have hn := (Unitary.norm_sub_one_lt_two_iff hu).2 hsp
  have he := expUnitary_argSelfAdjoint (u := ⟨c • A, hu⟩) hn
  have he2 : NormedSpace.exp (Complex.I • (Unitary.argSelfAdjoint ⟨c • A, hu⟩ : Matrix (Fin k) (Fin k) ℂ)) = c • A := by
    have := congrArg Subtype.val he
    rwa [selfAdjoint.expUnitary_coe] at this
  set S : Matrix (Fin k) (Fin k) ℂ := (Unitary.argSelfAdjoint ⟨c • A, hu⟩ : Matrix (Fin k) (Fin k) ℂ) with hS
  have hSs : Sᴴ = S := (Unitary.argSelfAdjoint ⟨c • A, hu⟩).2
  refine ⟨algebraMap ℂ _ (θ * Complex.I) + Complex.I • S, ?_, ?_⟩
  · rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hSs, Algebra.algebraMap_eq_smul_one,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp [add_comm]
  · let : NormedAlgebra ℚ (Matrix (Fin k) (Fin k) ℂ) := .restrictScalars ℚ ℂ _
    rw [NormedSpace.exp_add_of_commute (Algebra.commutes _ _), he2, ← NormedSpace.algebraMap_exp_comm,
      ← Complex.exp_eq_exp_ℂ, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul, hc, ← Complex.exp_add]
    simp
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
