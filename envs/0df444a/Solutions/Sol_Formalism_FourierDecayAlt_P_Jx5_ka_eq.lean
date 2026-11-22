-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx5.ka_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:58:15.170426+00:00
-- url     : https://prove2.me/submissions/c0c669c8-37fd-4dfe-bd43-50f4be51d9f3

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Jx5_rd_pos__157dd2cb063d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx5
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (G : Sz.Glob (InfinitePlace E)) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)
namespace Formalism.FourierDecayAlt.P.Jx5
theorem _root_.solution (hv : G.v = S6.rd E / 2) : G.ka = 2 * Real.pi / S6.rd E := by
  have hrd := rd_pos' (E := E)
  unfold Sz.Glob.ka; rw [hv]; field_simp
end Formalism.FourierDecayAlt.P.Jx5
