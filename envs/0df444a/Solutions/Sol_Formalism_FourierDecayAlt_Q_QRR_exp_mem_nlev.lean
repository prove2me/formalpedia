-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.exp_mem_nlev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:17:37.281798+00:00
-- url     : https://prove2.me/submissions/8d1cd496-74ac-4475-ad4d-a0280903e0ab

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_hpk_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_entry_zero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_sq_apply
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_cube
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_exp_of_cube
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_mulVec_bvec
import Theorems.Thm_Formalism_QuantumDeterminants_hermitian_pos_facts_hold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
private lemma gent_lemma_2 {l : Fin r} {Y : Mx k r} (hY : Pat k r l Y) (i j : Fin (2 * r + k + 1))
    (h1 : ¬ ((i.val = l.val ∧ l.val < j.val ∧ j.val ≤ 2 * r + k - l.val) ∨
      (j.val = 2 * r + k - l.val ∧ l.val ≤ i.val ∧ i.val < 2 * r + k - l.val)))
    (h2 : ¬ (i.val = l.val ∧ j.val = 2 * r + k - l.val)) :
    (1 + Y + (1 / 2 : ℂ) • (Y * Y)) i j = (1 : Mx k r) i j := by
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, pat_entry_zero hY i j h1,
    pat_sq_apply hY i j h2, smul_zero, add_zero, add_zero]
end Formalism.FourierDecayAlt.Q.QRR
end
end

set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.QRR
theorem _root_.solution {l : Fin r} {Y : Mx k r} (hY : Pat k r l Y) (hS : dag k r Y = -Y) :
    NormedSpace.exp Y ∈ Nlev k r l.castSucc := by
  have h2 : Hpk k r * Hpk k r = 1 := (hermitian_pos_facts_hold k r).2.1
  have h2' : ∀ M : Mx k r, Hpk k r * (Hpk k r * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hYc : Yᴴ = Hpk k r * (-Y) * Hpk k r := by
    have e : (Hpk k r)⁻¹ * Yᴴ * Hpk k r = -Y := hS
    rw [hpk_inv] at e
    calc Yᴴ = Hpk k r * (Hpk k r * Yᴴ * Hpk k r) * Hpk k r := by
          simp only [Matrix.mul_assoc, h2', h2, Matrix.mul_one]
      _ = _ := by rw [e]
  have hU : IsUnit (Hpk k r) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h2)
  have hc := Matrix.exp_conj (Hpk k r) (-Y) hU
  rw [hpk_inv] at hc
  have hUH : NormedSpace.exp Y ∈ UH (Hpk k r) := by
    show (NormedSpace.exp Y)ᴴ * Hpk k r * NormedSpace.exp Y = Hpk k r
    rw [← Matrix.exp_conjTranspose, hYc, hc,
      Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-Y)) (Hpk k r) (Hpk k r), h2, Matrix.mul_one,
      Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)),
      neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]
  rw [exp_of_cube (pat_cube hY)] at hUH ⊢
  have hl := l.isLt
  refine ⟨⟨hUH, fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩, hUH, fun a ha => ⟨?_, ?_⟩⟩
  · have ha := a.isLt
    have e1 : (eI k r a).val = a.val := rfl
    rw [gent_lemma_2 hY _ _ (by rw [e1]; omega) (by rw [e1]; omega)]
    exact Matrix.one_apply
  · rw [gent_lemma_2 hY _ _ (by omega) (by omega)]
    exact Matrix.one_apply
  · have ha' : a.val < l.val := ha
    have ha2 := a.isLt
    have e1 : (eI k r a).val = a.val := rfl
    rw [mulVec_bvec]
    funext p
    rw [gent_lemma_2 hY _ _ (by rw [e1]; omega) (by rw [e1]; omega)]
    simp [bvec, Pi.single_apply, Matrix.one_apply]
  · have ha' : a.val < l.val := ha
    have ha2 := a.isLt
    have e1 : (esI k r a).val = 2 * r + k - a.val := rfl
    rw [mulVec_bvec]
    funext p
    rw [gent_lemma_2 hY _ _ (by rw [e1]; omega) (by rw [e1]; omega)]
    simp [bvec, Pi.single_apply, Matrix.one_apply]
end Formalism.FourierDecayAlt.Q.QRR
