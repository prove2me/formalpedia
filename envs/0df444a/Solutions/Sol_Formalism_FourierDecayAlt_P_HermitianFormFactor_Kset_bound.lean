-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Kset_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:41:06.015935+00:00
-- url     : https://prove2.me/submissions/6b5308f9-ded0-47ee-989d-67bc644acf23

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_qf_factor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_entry_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_gram_trace
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_gram_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution {X : Q → Q → ℂ} {B : Q → P → ℂ} (h : (gramF X, B) ∈ Kset P Q 1) : ‖(X, B)‖ ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have h1' : (gram X).PosDef := h1
  have h2' : (Matrix.trace (gram X)).re ≤ 1 := h2
  have h3' : qf (gram X) (cm B) ≤ 1 ^ 2 := h3
  rw [gram_trace] at h2'
  have hu := gram_unit h1'
  have hinv : (gram X)⁻¹ = (((cm X)⁻¹)ᴴ)ᴴ * ((cm X)⁻¹)ᴴ := by
    rw [gram, Matrix.mul_inv_rev, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv]
  rw [qf_factor hinv, Matrix.conjTranspose_conjTranspose, one_pow] at h3'
  have hM : ∑ i, ∑ j, Complex.normSq (cm X i j) ≤ 1 := by
    rw [Finset.sum_comm]; exact h2'
  have hB : ∀ i j, ‖B j i‖ ≤ 1 := by
    intro i j
    have := entry_bound _ _ h3' hM i j
    rwa [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one] at this
  have hX : ∀ i j, ‖X i j‖ ≤ 1 := by
    intro i j
    have e1 : Complex.normSq (X i j) ≤ 1 := by
      refine le_trans ?_ h2'
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (X i j))
        (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j => Complex.normSq (X i j)) (fun j _ => Complex.normSq_nonneg _)
        (Finset.mem_univ j)
    rw [Complex.normSq_eq_norm_sq] at e1
    nlinarith [norm_nonneg (X i j)]
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => hX i j
  · exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => hB i j
end Formalism.FourierDecayAlt.P.HermitianFormFactor
