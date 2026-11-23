-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.lowJ_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:23.358859+00:00
-- url     : https://prove2.me/submissions/aca72322-947f-48f8-abb4-c6eceda17b0b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_blkM_isInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_int_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_lowJ_m
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
variable {K : Type} [CommRing K] {h g w : Point K} (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (R : Subring K) (a : lowW K h.1 h.2 × lowW K g.1 g.2)
    (ρ : Matrix (Fin g.1.sum) (Fin h.1.sum) K) :
    lowJ hN hW a ρ ∈ intSub R (lowW K w.1 w.2) ↔
      (a.1 ∈ intSub R (lowW K h.1 h.2) ∧ a.2 ∈ intSub R (lowW K g.1 g.2)) ∧ ∀ i j, ρ i j ∈ R := by
  rw [sec_mem_int (R := R) (g := lowJ hN hW a ρ) (by
      rw [lowJ_m]
      exact isLowUni_det K ((blkM_isLowUni _ _ _ _ _).2 ⟨a.1.2.1, rfl, a.2.2.1⟩)),
    sec_mem_int (R := R) (g := a.1) (isLowUni_det K a.1.2.1),
    sec_mem_int (R := R) (g := a.2) (isLowUni_det K a.2.2.1), lowJ_m, blkM_isInt]
  constructor
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨⟨h1, h4⟩, ?_⟩
    have hinv := ((sec_mem_int (R := R) (g := a.1) (isLowUni_det K a.1.2.1)).2 h1).2
    have e : ρ = ρ * sec_m a.1 * (((a.1 : GL (Fin h.1.sum) K)⁻¹ : GL (Fin h.1.sum) K) :
        Matrix (Fin h.1.sum) (Fin h.1.sum) K) := by
      rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    intro i j
    rw [e]
    exact int_mul R h3 hinv i j
  · rintro ⟨⟨h1, h4⟩, h3⟩
    exact ⟨h1, fun i j => by simp, int_mul R h3 h1, h4⟩
end Formalism.FourierDecayAlt.P.TwoBlockPoint
