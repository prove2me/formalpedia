-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.upJ_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:59.322012+00:00
-- url     : https://prove2.me/submissions/94814b62-a257-42ab-b125-ce1b4ea237d6

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_upJ_m
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
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] {h g w : Point K} (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution {u u' : upUniG K h.1.sum × upUniG K g.1.sum}
    {η η' : Matrix (Fin h.1.sum) (Fin g.1.sum) K}
    (e : (upJ hN u η : upUniG K w.1.sum) = upJ hN u' η') : u = u' ∧ η = η' := by
  have e1 := congrArg sec_m e
  rw [upJ_m, upJ_m] at e1
  obtain ⟨h1, h2, -, h4⟩ := blkM_inj hN e1
  have hu1 : u.1 = u'.1 := sec_m_ext h1
  refine ⟨Prod.ext hu1 (sec_m_ext h4), ?_⟩
  rw [hu1] at h2
  have hu : ∀ M : Matrix (Fin h.1.sum) (Fin g.1.sum) K,
      (((u'.1 : GL (Fin h.1.sum) K)⁻¹ : GL (Fin h.1.sum) K) : Matrix (Fin h.1.sum) (Fin h.1.sum) K) *
        (sec_m u'.1 * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [← hu η, h2, hu η']
end Formalism.FourierDecayAlt.P.TwoBlockPoint
