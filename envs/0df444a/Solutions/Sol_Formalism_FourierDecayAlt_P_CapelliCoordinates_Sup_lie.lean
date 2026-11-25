-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliCoordinates.Sup.lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:06:29.98236+00:00
-- url     : https://prove2.me/submissions/3ffef44d-a07e-4bfb-8c8b-c6a1f98b18ec

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpk_h
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hinv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hsq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_EabGlW_hsq__e5d4b9ac7468


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.CapelliCoordinates
variable {k r : ℕ} {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.CapelliCoordinates
namespace Sup
theorem _root_.solution {Z : Mx k r} (hZ : Sup k r i Z) :
    inLieLev k r i (hpart1 (Hpk k r) Z) ∧ inLieLev k r i (hpart2 (Hpk k r) Z) := by
  have hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv Qx2.hpk_sq'
  have hh : (Hpk k r)ᴴ = Hpk k r := Qx2.hpk_h
  have hsq : Hpk k r * Hpk k r = 1 := Qx2.hpk_sq'
  have hsq' : ∀ X : Mx k r, Hpk k r * (Hpk k r * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hsq, Matrix.one_mul]
  have hout : ∀ a : Fin r, a.val < i.val → ¬ Qx2.inV k r i (eI k r a) ∧ ¬ Qx2.inV k r i (esI k r a) := by
    intro a ha
    have := i.isLt
    simp only [Qx2.inV, eI, esI, Fin.val_mk]
    omega
  have hst1 : star (1 / 2 : ℂ) = 1 / 2 := by
    apply Complex.ext <;> simp
  have hst2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    rw [inv2I]
    apply Complex.ext <;> simp <;> norm_num
  refine ⟨⟨?_, fun a ha => ?_⟩, ⟨?_, fun a ha => ?_⟩⟩
  · simp only [hpart1, hinv, conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
      hh, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hsq, hsq',
      Matrix.mul_one, hst1]
    module
  · obtain ⟨h1, h2⟩ := hout a ha
    refine ⟨?_, ?_⟩
    · rw [hpart1, hinv, Matrix.smul_mulVec, Matrix.sub_mulVec, (hZ _ h1).1, (hZ _ h1).2, sub_zero, smul_zero]
    · rw [hpart1, hinv, Matrix.smul_mulVec, Matrix.sub_mulVec, (hZ _ h2).1, (hZ _ h2).2, sub_zero, smul_zero]
  · simp only [hpart2, hinv, conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
      hh, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hsq, hsq',
      Matrix.mul_one, hst2]
    module
  · obtain ⟨h1, h2⟩ := hout a ha
    refine ⟨?_, ?_⟩
    · rw [hpart2, hinv, Matrix.smul_mulVec, Matrix.add_mulVec, (hZ _ h1).1, (hZ _ h1).2, add_zero, smul_zero]
    · rw [hpart2, hinv, Matrix.smul_mulVec, Matrix.add_mulVec, (hZ _ h2).1, (hZ _ h2).2, add_zero, smul_zero]
end Sup
end Formalism.FourierDecayAlt.P.CapelliCoordinates
