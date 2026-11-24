-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.PhiH_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:07.772141+00:00
-- url     : https://prove2.me/submissions/550453ee-f9b9-43bc-a797-da4218204991

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_blkM_isInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_Fz_perturb
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_bigZ_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_bigZ_add
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_blkM_isInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (ψ : AddChar K ℂ) (h : Point K) {n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K)
    (ϖ : K) (hϖ : ϖ ∈ R) (hu : ∀ r ∈ R, ∃ y ∈ R, (1 + ϖ * r) * y = 1) (k j : ℕ)
    (hj : ϖ ^ j * (pt h.1 h.2).det ^ 2 ∈ R) (s : ℕ) (G E : Matrix (Fin s) (Fin s) K) (c : K)
    (hc : G.det * c = 1) (hck : ϖ ^ k * c ∈ R)
    (hE : ∀ i l, ∃ r ∈ R, E i l = (pt h.1 h.2).det ^ 2 * ϖ ^ (2 * k + 1 + j) * r) :
    PhiH R ψ h Z' s (G + E) = PhiH R ψ h Z' s G := by
  have hdpt := pt_unit_lemma_5 h.1 h.2
  have hdG : IsUnit G.det := ⟨⟨G.det, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩
  unfold PhiH
  refine finsum_congr fun τ => ?_
  congr 1
  rw [bigZ_add]
  have hdZ : (orbZ h (rep R τ.1)).det = (pt h.1 h.2).det := by
    unfold orbZ
    rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det K (rep R τ.1).1.2.1, isUpUni_det K (rep R τ.1).2.2]
    ring
  have hdet : (bigZ rfl (orbZ h (rep R τ.1)) (outM R τ.2.1) (outM R τ.2.2) G).det =
      (pt h.1 h.2).det * G.det := by
    rw [bigZ_det, hdZ]
  have hEm : ∀ i l, E i l ∈ R := by
    intro i l
    obtain ⟨r, hr, e⟩ := hE i l
    rw [e, show (pt h.1 h.2).det ^ 2 * ϖ ^ (2 * k + 1 + j) * r =
      ϖ ^ j * (pt h.1 h.2).det ^ 2 * ϖ ^ (2 * k + 1) * r by ring]
    exact R.mul_mem (R.mul_mem hj (R.pow_mem hϖ _)) hr
  apply Fz_perturb R ϖ hϖ hu Z'
  · rw [hdet]
    exact hdpt.mul hdG
  · exact (blkM_isInt rfl 0 0 0 E R).2 ⟨by intro i l; simp, by intro i l; simp, by intro i l; simp, hEm⟩
  · intro x y
    rw [hdet]
    obtain ⟨p, rfl⟩ := (eN (rfl : h.1.sum + s = h.1.sum + s)).surjective x
    obtain ⟨q, rfl⟩ := (eN (rfl : h.1.sum + s = h.1.sum + s)).surjective y
    rcases p with p | p <;> rcases q with q | q
    · exact ⟨0, R.zero_mem, by simp [blkM_ll]⟩
    · exact ⟨0, R.zero_mem, by simp [blkM_lr]⟩
    · exact ⟨0, R.zero_mem, by simp [blkM_rl]⟩
    · obtain ⟨r, hr, e⟩ := hE p q
      refine ⟨ϖ ^ j * (ϖ ^ k * c) ^ 2 * r,
        R.mul_mem (R.mul_mem (R.pow_mem hϖ _) (R.pow_mem hck _)) hr, ?_⟩
      rw [blkM_rr, e]
      linear_combination (-((pt h.1 h.2).det ^ 2 * ϖ ^ (2 * k + 1 + j) * r * (G.det * c + 1))) * hc
end Formalism.FourierDecayAlt.P.TwoBlockPoint
