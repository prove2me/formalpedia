-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx6.baseGram_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:20.433306+00:00
-- url     : https://prove2.me/submissions/1388341e-ece6-4ff6-ab14-4fb3b1faf664

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_sum_mul_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx6
namespace Formalism.FourierDecayAlt.P.Jx6
theorem _root_.solution {E W : Type} [Field E] (D : TB.Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ}
    (hε : 0 < ε) (k : ℕ) (w : W) (Y : Finset (TB.Pt E)) {κ : TB.Pt E → TB.Pt E → ℂ}
    (hκ : TB.PSDOn Y κ) : 0 ≤ D.N0 ε k w Y κ := by
  unfold TB.Data.N0
  exact div_nonneg (sum_mul_nonneg hκ (hG ε hε k w Y)) (hW w).le
end Formalism.FourierDecayAlt.P.Jx6
