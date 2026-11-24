-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.qf_definite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:21:21.856573+00:00
-- url     : https://prove2.me/submissions/2e31f99d-6601-418f-bf61-cfc68cc506e3

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_posDef_factor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_qf_factor

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
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution {T : Matrix Q Q ℂ} (hT : T.PosDef) (B : Matrix P Q ℂ) (h : qf T B ≤ 0) : B = 0 := by
  obtain ⟨a, ha, hTa⟩ := posDef_factor hT.inv
  rw [qf_factor hTa] at h
  have hnn : ∀ i, 0 ≤ ∑ j, Complex.normSq ((B * aᴴ) i j) :=
    fun i => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have h1 : ∑ i, ∑ j, Complex.normSq ((B * aᴴ) i j) = 0 :=
    le_antisymm h (Finset.sum_nonneg fun i _ => hnn i)
  have h0 : B * aᴴ = 0 := by
    ext i j
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).mp h1 i (Finset.mem_univ _)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).mp h2 j (Finset.mem_univ _)
    simpa using h3
  have ha' : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact ha.star
  calc B = B * aᴴ * (aᴴ)⁻¹ := by rw [Matrix.mul_nonsing_inv_cancel_right _ _ ha']
    _ = 0 := by rw [h0, Matrix.zero_mul]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
