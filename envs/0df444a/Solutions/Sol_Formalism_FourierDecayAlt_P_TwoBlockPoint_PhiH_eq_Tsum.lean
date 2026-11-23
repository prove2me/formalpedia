-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.PhiH_eq_Tsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:55.759049+00:00
-- url     : https://prove2.me/submissions/d374220c-a3ea-4ecc-b017-edb8b6d89d21

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
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
variable {K : Type} [CommRing K] (R : Subring K)
variable {a s : ℕ}
variable {N : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (ψ : AddChar K ℂ) (h : Point K) {n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K)
    (n : ℕ) (G : Matrix (Fin n) (Fin n) K) :
    PhiH R ψ h Z' n G =
      ∑ᶠ τ : Cos R h × Matrix (Fin n) (Fin h.1.sum) (KR R) × Matrix (Fin h.1.sum) (Fin n) (KR R),
        Tsum R ψ Z' (orbZ h (rep R τ.1)) (outM R τ.2.1) (outM R τ.2.2) G * phase ψ (rep R τ.1) := by
  unfold PhiH Tsum
  exact finsum_congr fun τ => by ring
end Formalism.FourierDecayAlt.P.TwoBlockPoint
