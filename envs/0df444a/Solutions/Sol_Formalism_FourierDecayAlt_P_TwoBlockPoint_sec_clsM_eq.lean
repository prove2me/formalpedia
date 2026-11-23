-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.sec_clsM_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:19.131432+00:00
-- url     : https://prove2.me/submissions/ef695b9a-09a5-4364-82a0-1a2878ba00ce

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
variable {K : Type} [CommRing K] (R : Subring K) {ι κ μ : Type}
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (x x' : Matrix ι κ K) : clsM R x = clsM R x' ↔ ∀ i j, (x' - x) i j ∈ R := by
  rw [eq_comm]
  constructor
  · intro h i j
    have h1 := congrFun (congrFun h i) j
    change Submodule.Quotient.mk (x' i j) = Submodule.Quotient.mk (x i j) at h1
    rw [Submodule.Quotient.eq, LinearMap.mem_range] at h1
    obtain ⟨r, hr⟩ := h1
    rw [Matrix.sub_apply, ← hr]
    exact r.2
  · intro h
    ext i j
    change Submodule.Quotient.mk (x' i j) = Submodule.Quotient.mk (x i j)
    rw [Submodule.Quotient.eq, LinearMap.mem_range]
    exact ⟨⟨_, h i j⟩, rfl⟩
end Formalism.FourierDecayAlt.P.TwoBlockPoint
