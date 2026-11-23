-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.lowJ_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:40.73782+00:00
-- url     : https://prove2.me/submissions/95366cf5-35ee-456c-9c2e-6da6235ea1f9

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_lowJ_m
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
theorem _root_.solution {v v' : lowW K h.1 h.2 × lowW K g.1 g.2}
    {ξ ξ' : Matrix (Fin g.1.sum) (Fin h.1.sum) K}
    (e : lowJ hN hW v ξ = lowJ hN hW v' ξ') : v = v' ∧ ξ = ξ' := by
  have e1 := congrArg sec_m e
  rw [lowJ_m, lowJ_m] at e1
  obtain ⟨h1, -, h3, h4⟩ := blkM_inj hN e1
  have hv1 : v.1 = v'.1 := sec_m_ext h1
  refine ⟨Prod.ext hv1 (sec_m_ext h4), ?_⟩
  rw [hv1] at h3
  have hv : ∀ M : Matrix (Fin g.1.sum) (Fin h.1.sum) K,
      M * sec_m v'.1 * (((v'.1 : GL (Fin h.1.sum) K)⁻¹ : GL (Fin h.1.sum) K) :
        Matrix (Fin h.1.sum) (Fin h.1.sum) K) = M := by
    intro M
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [← hv ξ, h3, hv ξ']
end Formalism.FourierDecayAlt.P.TwoBlockPoint
