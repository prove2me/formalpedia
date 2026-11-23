-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.rk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:16.138346+00:00
-- url     : https://prove2.me/submissions/e51bb182-5657-41c5-b7f2-549a9c637dce

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_finrank_zsub
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_rk_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_rk_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x3
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x3
theorem _root_.solution (A : FI E) (s : ℕ) (hA0 : A ≠ 0) (hA : ConjStable E A) :
    finrank ℤ (eig E A s) = deg E := by
  have h1 := rk_add E A s hA
  rw [rk_succ, finrank_zsub E A hA0] at h1
  have h2 : finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [h2] at h3
  unfold deg
  omega
end Formalism.FourierDecayAlt.P.S6x3
