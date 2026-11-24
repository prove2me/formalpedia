-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorExpansion.of_Xf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:14.081954+00:00
-- url     : https://prove2.me/submissions/d2dfee93-ba3d-4ffa-9f6f-9b70dbd334df

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorExpansion_sq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QuantumMinorExpansion
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.Qx6
variable {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 2) → Fin (m + 2) → A)
namespace Formalism.FourierDecayAlt.P.QuantumMinorExpansion
theorem _root_.solution (σ : ℤ) (u : ℂ) (q : Fin (m + 2)) (i' : Fin (m + 1)) (j : Fin (m + 2))
    (h : ∀ p, Xf E σ q i' j u p = 0) :
    (qminor E (q.succAbove i').succAbove j.succAbove (u + 1) * qminor E q.succAbove j.succAbove u -
      qminor E q.succAbove j.succAbove (u + 1) * qminor E (q.succAbove i').succAbove j.succAbove u = 0) ∧
    ∀ x : Fin (m + 1),
      qminor E (q.succAbove i').succAbove j.succAbove (u + 1) * qminor E q.succAbove (j.succAbove x).succAbove u -
        qminor E q.succAbove j.succAbove (u + 1) * qminor E (q.succAbove i').succAbove (j.succAbove x).succAbove u =
      (((-1) ^ ((j.succAbove x : Fin (m + 2)) : ℕ) * (σ * (-1) ^ (x : ℕ)) : ℤ) : A) *
        (qdet E (u + 1) * qminor E (q.succAbove ∘ i'.succAbove) (j.succAbove ∘ x.succAbove) u) := by
  constructor
  · have h0 := h j
    unfold Xf at h0
    rw [Fin.insertNth_apply_same, sub_zero] at h0
    have h1 := congrArg (fun y => ((-1 : ℤ) ^ (j : ℕ)) • y) h0
    simp only [smul_smul, sq_one, one_smul, smul_zero] at h1
    exact h1
  · intro x
    have h0 := h (j.succAbove x)
    unfold Xf at h0
    rw [Fin.insertNth_apply_succAbove, sub_eq_zero] at h0
    have h1 := congrArg (fun y => ((-1 : ℤ) ^ ((j.succAbove x : Fin (m + 2)) : ℕ)) • y) h0
    simp only [smul_smul, sq_one, one_smul] at h1
    rw [h1, zsmul_eq_mul]
end Formalism.FourierDecayAlt.P.QuantumMinorExpansion
